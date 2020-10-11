from docutils import nodes
from docutils.parsers.rst import Directive, directives
from docutils.parsers.rst.directives.images import Figure
from docutils.parsers.rst.directives.tables import RSTTable
from sphinx.roles import XRefRole
from sphinx.addnodes import start_of_file
from pprint import pprint

def setup(app):
    app.add_config_value('numbered_blocks', [], 'html')

    # new nodes
    app.add_node(numbered_block, html=(visit_numbered_block_html, depart_numbered_block_html),
                 latex=(visit_numbered_block_latex, depart_numbered_block_latex))
    app.add_node(numbered_block_ref, html=(visit_numbered_block_ref_html, None),
                 latex=(visit_numbered_block_ref_latex,None))
    app.add_node(numbered_block_title, html=(visit_numbered_block_title_html, depart_numbered_block_title_html),
                 latex=(visit_numbered_block_title_latex, depart_numbered_block_title_latex))

    app.connect('builder-inited', builder_inited)
    app.connect('env-purge-doc', env_purge_doc)
    app.connect('doctree-read', doctree_read)
    app.connect('doctree-resolved', doctree_resolved)

# Visitor Functions for the new nodes
# -- HTML
def visit_numbered_block_html(self, node):
    self.body.append(self.starttag(node, 'div'))

def depart_numbered_block_html(self, node):
    self.body.append('</div>\n')

def visit_numbered_block_title_html(self, node):
    self.body.append(self.starttag(node, 'span', CLASS='title'))
    pass

def depart_numbered_block_title_html(self, node):
    self.body.append('</span>')
    pass

def visit_numbered_block_ref_html(self, node):
    self.SkipNode

# -- LaTeX
def visit_numbered_block_latex(self,node):
    pass

def depart_numbered_block_latex(self, node):
    pass

def visit_numbered_block_title_latex(self,node):
    pass

def depart_numbered_block_title_latex(self,node):
    pass

def visit_numbered_block_ref_latex(self, node):
    self.SkipNode

class numbered_block(nodes.General, nodes.Element): pass
class numbered_block_title(nodes.General, nodes.Element): pass
class numbered_block_ref(nodes.reference): pass

class NumberedElement(Directive):

    has_content = True
    required_arguments = 0
    optional_arguments = 1  # Title
    final_argument_whitespace = True

    option_spec = {
            'name' : directives.unchanged,
            'id'   : directives.unchanged,
            'class' : directives.class_option,
            'nonumber': directives.flag,
    }

    def numbered(self):
        env = self.state.document.settings.env
        definitions = env.numbered_blocks_definitions
        return definitions[self.name]['numbered'] and 'nonumber' not in self.options


class NumberedBlock(NumberedElement):

    def run(self):
        env = self.state.document.settings.env
        definitions = env.numbered_blocks_definitions
        head, tail = definitions[self.name]['wrap-content'].split('%s')
        head = nodes.raw(head, head, format='html')
        tail = nodes.raw(tail, tail, format='html')

        if 'name' in self.options and len(self.options['name'].split('+')) > 1:
            env.app.warn("Invalid '+' in name '%s'" %  self.options['name'])

        node = numbered_block(**self.options)
        if 'id' in self.options:
            id = nodes.fully_normalize_name(self.options['id'])
        else:
            id = "%s-%d" % (self.name, env.new_serialno(self.name))

        node['ids'] = [id]
        node['classes'].append('numbered-block')
        node['classes'].append(self.name)
        node['type'] = self.name
        numbered = self.numbered()
        node['numbered'] = numbered

        if not numbered:
            node['classes'].append('nonumber')

        self.add_name(node)
        self.state.nested_parse(self.content, self.content_offset, node)

        # Add title nodes
        messages = []
        if self.arguments or numbered:
            title = numbered_block_title()

            if self.arguments:
                title_text = definitions[self.name]['title-format'] % self.arguments[0]
                title_nodes, messages = self.state.inline_text(title_text, 0)
                for title_node in title_nodes:
                    title.append(title_node)

                if numbered:
                    title.insert(0, nodes.inline('', definitions[self.name]['title-separator'], classes=['separator']))

            if definitions[self.name]['title-position'] == 'bottom':
                node.append(title)
            else:
                node.insert(0, title)

        node.insert(0, head)
        node.append(tail)
        return [node] + messages


class NumberedFigure(Figure):

    option_spec = Figure.option_spec.copy()
    option_spec['nonumber'] = directives.flag

    def run(self):
        env = self.state.document.settings.env
        definitions = env.numbered_blocks_definitions

        (figure,) = Figure.run(self)
        if isinstance(figure, nodes.system_message):
            return [figure]

        id = "%s-%d" % (self.name, env.new_serialno(self.name))
        figure['ids'] = [id]
        figure['classes'].append('numbered-block')
        figure['type'] = self.name
        numbered = definitions[self.name]['numbered'] and 'nonumber' not in self.options
        figure['numbered'] = numbered

        # Move name from image to figure and register as target
        image = figure.children[figure.first_child_matching_class(nodes.image)]
        if len(image['names']) > 0:
            name = image['names'][0]
            figure['names'] = [name]
            if name in self.state.document.nameids:
                del(self.state.document.nameids[name])
            self.state.document.note_explicit_target(figure)

        # Prepare caption
        caption_pos = figure.first_child_matching_class(nodes.caption)
        if numbered:
            if not caption_pos:
                figure.append(nodes.caption('', ''))
            else:
                caption = figure.children[caption_pos]
                caption.insert(0, nodes.inline('', definitions[self.name]['title-separator'], classes=['separator']))

        return [figure]


class NumberedTable(NumberedElement, RSTTable):

    option_spec = NumberedElement.option_spec.copy()
    option_spec.update(RSTTable.option_spec.copy())

    def run(self):
        env = self.state.document.settings.env
        definitions = env.numbered_blocks_definitions

        (table,) = RSTTable.run(self)
        if isinstance(table, nodes.system_message):
            return [table]

        numbered = self.numbered()
        if not table['ids']:
            id = "%s-%d" % (self.name, env.new_serialno(self.name))
            table['ids'] = [nodes.fully_normalize_name(id)]
            self.add_name(table)

        table['classes'].append('numbered-block')
        table['type'] = self.name
        table['numbered'] = numbered

        title_pos = table.first_child_matching_class(nodes.title)
        if numbered:
            if title_pos == None:
                table.insert(0, nodes.title('', ''))
            else:
                title = table.children[title_pos]
                title.insert(0, nodes.inline('', definitions[self.name]['title-separator'], classes=['separator']))

        return [table]


def builder_inited(app):
    dict = getattr(app.env, 'numbered_blocks_definitions', {})

    for definition in app.config.numbered_blocks:
        if 'name' not in definition:
            app.warn("Invalid definition: %s" % definition)
            continue
        type = definition['name']
        if type == 'figure':
            app.add_directive(type, NumberedFigure)
        elif type == 'table':
            app.add_directive(type, NumberedTable)
        else:
            app.add_directive(type, NumberedBlock)

        if 'label-format' not in definition:
            definition['label-format'] = type.capitalize() + ' %s'
        if 'reference-format' not in definition:
            definition['reference-format'] = definition['label-format']
        if 'title-format' not in definition:
            definition['title-format'] = '%s'
        if 'title-separator' not in definition:
            definition['title-separator'] = ': '
        if 'reference' not in definition:
            definition['reference'] = type + '-ref'
        if 'numbered' not in definition:
            definition['numbered'] = True
        if 'wrap-content' not in definition:
            definition['wrap-content'] = '%s';
        if 'counter' not in definition:
            definition['counter'] = type;
        if 'title-position' not in definition:
            definition['title-position'] = 'top'
        if 'numbering-level' not in definition:
            definition['numbering-level'] = 1
        if 'numbering-style' not in definition:
            definition['numbering-style'] = 'arabic'
        elif definition['title-position'] not in ('top','bottom'):
            app.error('Invalid title position: %s' % definition['title-position'])

        dict[type] = definition

        if definition['reference']:
            app.add_role(definition['reference'], XRefRole(nodeclass=numbered_block_ref))

        app.env.numbered_blocks_definitions = dict


def env_purge_doc(app, env, docname):
    first_pass = getattr(env, 'numbered_blocks_first_pass', False)
    if not first_pass:
        env.numbered_blocks_first_pass = True


def doctree_read(app, doctree):
    env = app.builder.env
    blocks = getattr(env, 'numbered_blocks_by_id', {})
    definition = getattr(env, 'numbered_blocks_definitions', {})

    if env.docname not in blocks:
        blocks[env.docname] = {}

    for section in doctree.traverse(nodes.section):

        counts = {}     # block count per chapter
        for node in section.traverse(lambda n: isinstance(n, numbered_block)
                                            or isinstance(n, nodes.figure)
                                            or isinstance(n, nodes.table)):
            if not 'numbered' in node:
                # Not a directive
                continue

            id = node['ids'][0]
            type = node['type']
            depth = 0
            parent = section.parent
            while not isinstance(parent,nodes.document):

                depth += 1
                parent = parent.parent


            if depth > definition[type]['numbering-level']:
                continue

            counter = definition[type]['counter']
            if counter not in counts:
                counts[counter] = 1

            entry = {'docname': env.docname,
                     'id': id,
                     'type': type,
                     'anchorname': '#' + section['ids'][0]}

            if node.get('names'):
                entry['name'] = node['names'][0]

            if not node['numbered']:
                entry['count'] = False
            else:
                entry['count'] = counts[counter]
                counts[counter] += 1
            
            blocks[env.docname][id] = entry

    env.numbered_blocks_by_id = blocks


def build_labels(app, doctree, docname, idprefix=''):
    env = app.builder.env
    blocks = getattr(env, 'numbered_blocks_by_id', {})
    definition = getattr(env, 'numbered_blocks_definitions', {})
    for node in doctree.traverse(lambda n: isinstance(n, numbered_block)
                                        or isinstance(n, nodes.figure)
                                        or isinstance(n, nodes.table)):
        if not 'numbered' in node:
            continue
        id = node['ids'][0]
        block = blocks[docname][id]
        type = block['type']
        node['ids'][0] = idprefix + node['ids'][0]
        if block['number']:
            label = nodes.inline('', definition[type]['label-format'] % block['number'], classes=['label'])
            if type == 'figure':
                pos = node.first_child_matching_class(nodes.caption)
            elif type == 'table':
                pos = node.first_child_matching_class(nodes.title)
            else:
                pos = node.first_child_matching_class(numbered_block_title)

            node.children[pos].insert(0, label)


def doctree_resolved(app, doctree, fromdocname):
    env = app.builder.env
    blocks = getattr(env, 'numbered_blocks_by_id', {})
    definition = getattr(env, 'numbered_blocks_definitions', {})
    secnumbers = env.toc_secnumbers

    # Add section number
    for doc in blocks:
        for id, block in blocks[doc].items():
            anchorname = block['anchorname']
            target_doc = block['docname']
            if anchorname not in secnumbers[doc]:
                anchorname = ''
            if 'secnumber' not in block:
                block['secnumber'] = secnumbers[doc][anchorname][0]
            type = block['type']
            if block['count']:
                if definition[type]['numbering-level'] > 0:
                    block['number'] = '.'.join([str(item) for item in secnumbers[doc][anchorname][:definition[type]['numbering-level']]]) + \
                                               '.' + block_number(block['count'],definition[type]['numbering-style'])
                else:
                    block['number'] = block_number(block['count'],definition[type]['numbering-style'])
            else:
                block['number'] = False
    # Build labels
    files = doctree.traverse(start_of_file)
    if not files:
        build_labels(app, doctree, fromdocname)
    else:
        for file in files:
            if len(file.traverse(start_of_file)) > 1:   # not a leaf
                continue
            build_labels(app, file, file['docname'], ("document-%s-" % file['docname']))

    # Resolve references
    anonlabels = env.domains['std'].data['anonlabels']
    for ref in doctree.traverse(numbered_block_ref):
        target = nodes.fully_normalize_name(ref['reftarget']).split('+')
        postfix = target[1] if len(target) > 1 else ''
        target = target[0]
        target_doc, id = anonlabels.get(target, ('',False))

        if not id or id not in blocks[target_doc]:
            app.warn('Target block not found: %s' % target)
            label = target
            link = "#%s" % target

        else:
            block = blocks[target_doc][id]
            type = block['type']
            if block['number']:
                label = definition[type]['reference-format'] % block['number'] + postfix
            else:
                label = target
            link = app.builder.get_relative_uri(fromdocname, block['docname'])
            link += '#' if link.find('#') == -1 else '-'
            link += block['id']

        if ref['refexplicit']:
            label = ref.astext()

        html = '<a href="%s">%s</a>' % (link, label)
        ref.replace_self(nodes.raw(html, html, format='html'))

def number_to_letter(number):
    # Takes a number and converts to Excel column letters, i.e. "A, B, ... Z, AA, AB..."
    # Lifted from https://stackoverflow.com/questions/297213/translate-a-column-index-into-an-excel-column-name
    letter = ''
    # Convert to zero indexed (i.e., 1 becomes 0, etc.)
    znumber = number - 1
    while 1:
        znumber, remainder = divmod(znumber, 26)
        letter = chr(remainder + ord('A')) + letter
        if not znumber:
            return letter
        znumber -= 1

def number_to_roman(num):
    # Takes a number and converts to roman numerals.
    # Copied from Aziz Alto in https://stackoverflow.com/questions/28777219/basic-program-to-convert-integer-to-roman-numerals
    num_map = [(1000, 'M'), (900, 'CM'), (500, 'D'), (400, 'CD'), (100, 'C'), (90, 'XC'),
           (50, 'L'), (40, 'XL'), (10, 'X'), (9, 'IX'), (5, 'V'), (4, 'IV'), (1, 'I')]

    roman = ''

    while num > 0:
        for i, r in num_map:
            while num >= i:
                roman += r
                num -= i

    return roman

def block_number(number, type):
    # Given a number and a type, return the block number as a string of the correct type.
    # Types can be {arabic|roman|Roman|alpha|Alpha}
    if type == 'arabic':
        return str(number)
    if type == 'Alpha':
        return number_to_letter(number)
    if type == 'alpha':
        return number_to_letter(number).lower()
    if type == 'Roman':
        return number_to_roman(number)
    if type == 'roman':
        return number_to_roman(number).lower()
