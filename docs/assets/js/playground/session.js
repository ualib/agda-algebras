// File: docs/assets/js/playground/session.js
//
// One run of the checker, planned command by command from Agda's own answers.
// The WASI host's paced stdin (`wasi.js`) calls `next` with everything Agda
// has written so far each time Agda has answered the last command and waits
// for another; `next` returns the next command line, or null to end the run.
// Pure but for `write`, the callback that replaces the reader's file in the
// guest's filesystem; `scripts/js/playground/test_session.mjs` drives it with
// recorded answers.
//
// The plan always has the same shape, as follows:
//
//   1.  Load the reader's text.  If that fails, stop: the reader needs the
//       error, and every further command would load the file again first.
//   2.  If the reader asked for something at a goal (a give, a refine, a case
//       split, or the type of an expression there), send it.  If Agda answers
//       with a change to the text, make the change in the guest's file and
//       load it again.  The second load is cheap: Agda keeps every imported
//       module in memory between loads in one process (measured, Setoid tier,
//       node 22: 12.5 s for the first load, 1.4 s for the reload).
//   3.  Ask for the type and context of every goal the last load left, by the
//       numbers that load reported, newest first in each context as Emacs
//       shows it.
//
// So every button on the page costs one run, and one cold load.

import { answers, command, readAction, readGoal, readLoad } from './protocol.js';
import { applyGive, applySplit } from './edits.js';

/** Plan one run.
 *
 * `path` is the reader's file as the guest sees it, `source` its text,
 * `action` null or `{op, goal, text}` with `op` one of give, refine, case,
 * have, `rewrite` the form for goal types, and `write(text)` replaces the
 * file in the guest.  `limit` bounds the commands sent, whatever happens. */
export function session({ path, source, action = null, rewrite = 'Simplified', write = () => {}, limit = 64 }) {
  const sent = [];          // the operations sent so far, in order
  let text = source;        // the text the guest's file holds now
  let done = false;
  let edited = false;
  let lastLoad = -1;        // index in `sent` of the load that describes `text`
  let queue = null;         // goal numbers whose context is still to ask for

  const send = (op) => {
    sent.push(op);
    if (op.op === 'load') lastLoad = sent.length - 1;
    return command(path, op);
  };
  const stop = () => { done = true; return null; };

  function next(output) {
    if (done) return null;
    if (sent.length >= limit) return stop();
    if (sent.length === 0) return send({ op: 'load' });

    const got = answers(output).answers;
    const k = sent.length - 1;
    const op = sent[k];
    const reply = got[k] || [];

    if (op.op === 'load') {
      const load = readLoad(reply);
      if (load.error) return stop();
      if (action && !sent.some((o) => o === action)) {
        sent.push(action);
        // A `have` shows the goal's type and context too, in the form the
        // reader chose for every other goal.
        return command(path, { rewrite, ...action });
      }
      queue = (load.points || load.goals).map((g) => g.id);
    } else if (op === action) {
      const result = readAction(reply);
      const changed = result.give ? applyGive(text, result.give, action.text || '')
        : result.split ? applySplit(text, result.split) : null;
      if (changed !== null) {
        text = changed;
        edited = true;
        write(text);
        return send({ op: 'load' });
      }
      queue = goalsOf(got[lastLoad] || []);
      // A `have` that Agda answered carries the goal's context already, so
      // it is not asked for twice; one Agda refused carries none, and the
      // goal's context is asked for like any other's.
      if (action.op === 'have' && readGoal(reply)) {
        queue = queue.filter((id) => id !== action.goal);
      }
    }

    if (queue === null) queue = goalsOf(got[lastLoad] || []);
    if (queue.length === 0) return stop();
    return send({ op: 'context', goal: queue.shift(), rewrite });
  }

  /** What the run found, read from all of Agda's output once it has exited:
   * the text as it ends (changed by an action, or not), the last load's
   * reading of it, the goals' contexts by number, and the action's answer. */
  function result(output) {
    const got = answers(output).answers;
    const actionAt = sent.indexOf(action);
    const contexts = {};
    sent.forEach((op, k) => {
      if (op.op !== 'context') return;
      const goal = readGoal(got[k] || []);
      if (goal) contexts[goal.id] = goal;
    });
    const reply = actionAt === -1 ? null : got[actionAt] || [];
    const have = action && action.op === 'have' && reply ? readGoal(reply) : null;
    if (have) contexts[have.id] = have;
    return {
      source: text,
      edited,
      sent: sent.map((op) => op.op),
      load: lastLoad === -1 ? null : readLoad(got[lastLoad] || []),
      firstLoad: sent.length ? readLoad(got[0] || []) : null,
      contexts,
      action: reply === null ? null : { ...readAction(reply), have: have ? have.have : null },
    };
  }

  return { next, result };
}

function goalsOf(loadReply) {
  const load = readLoad(loadReply);
  return (load.points || load.goals).map((g) => g.id);
}
