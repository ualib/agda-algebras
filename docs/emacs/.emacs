; init.el 
;
; Emacs custom initializaiton file
; modified [2013.07.23] by <williamdemeo@gmail.com>
; modified [2011.11.29] by <williamdemeo@gmail.com>
; modified [2009.04.26] by <williamdemeo@gmail.com>
; modified [2004.01.09] by <williamdemeo@yahoo.com>


;; Added by Package.el.  This must come before configurations of
;; installed packages.  Don't delete this line.  If you don't want it,
;; just comment it out by adding a semicolon to the start of the line.
;; You may delete these explanatory comments.
(package-initialize)

(message "Loading .emacs custom configuration file")

(scroll-bar-mode -1) ; ...what self-respecting emacs user wants a scrollbar?

;--geometry------------------------------------------------------------------------
(defun arrange-frame (w h x y)
  "Set the width, height, and x/y position of the current frame"
  (let ((frame (selected-frame)))
    (delete-other-windows)
    (set-frame-position frame x y)
    (set-frame-size frame w h)))

(when (display-graphic-p)
  (arrange-frame 139 76 0 0)  ; <<<< set the w h x y variables here
)

;--packages----------------------------------------------------------------
 (require 'package)
 (setq package-archives
       '(
       ("melpa-stable" . "http://stable.melpa.org/packages/")
       ("melpa"     . "http://melpa.milkbox.net/packages/")
       ;("marmalade" . "http://marmalade-repo.org/packages/")
       ("gnu"       . "http://elpa.gnu.org/packages/")))
 (package-initialize)

;-- Magit ------------------------------------------------------------
 ; Install magit
(unless (package-installed-p 'magit-status))
 ; If this fails, magit can also be installed after emacs starts as follows:
 ; `M-x package-refresh-contents` and `M-x package-install [Enter] magit`

(define-key global-map "\M-gm" 'magit-status)

;;;;--------- For Scala -------------------
;(unless (package-installed-p 'scala-mode2)
;  (package-refresh-contents) (package-install 'scala-mode2))
;;;;----------------------------------------------

;;; disable loading of "default.el" at startup
(setq inhibit-default-init t)

;; turn on font-lock mode
(when (fboundp 'global-font-lock-mode)
  (global-font-lock-mode t))

;; enable visual feedback on selections
;(setq transient-mark-mode t)

;; The rest was mainly taken from my old init.el file

;; Global key bindings
(define-key global-map "\C-cc" 'compile)
(define-key global-map "\C-cs" 'shell)
(define-key global-map "\C-cg" 'gdb)

;;  LaTeX Mode
;;
(setq auto-mode-alist
      (cons '("\\.tex$" . LaTeX-mode) auto-mode-alist))
(setq auto-mode-alist
      (cons '("\\.def$" . LaTeX-mode) auto-mode-alist))
(add-hook 'LaTeX-mode-hook
          (lambda ()
                           ; I've made peace with long lines.
      ; (auto-fill-mode 1) ; If you haven't, then uncomment this line.
	    (font-lock-mode 1)))
(add-hook 'LaTeX-mode-hook 'turn-on-reftex)   ; with AUCTeX LaTeX mode

(setq reftex-external-file-finders
      '(("tex" . "kpsewhich -format=.tex %f")
       ("bib" . "kpsewhich -format=.bib %f")))


 (add-hook 'latex-mode-hook
 	  (lambda ()
                           ; I've made peace with long lines.
      ; (auto-fill-mode t) ; If you haven't, then uncomment this line.
	    (reftex-mode t)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; The following lines are suggested by
;; https://tex.stackexchange.com/questions/124501/reftex-multiple-files-problems
(setq TeX-auto-save t)
(setq TeX-parse-self t)
(setq TeX-save-query nil)
(setq TeX-PDF-mode t)
(setq-default TeX-master nil)
(require 'tex-site)
(setq reftex-enable-partial-scans t)
(setq reftex-save-parse-info t)
(setq reftex-use-multiple-selection-buffers t)
(setq reftex-plug-into-AUCTeX t)
(autoload 'reftex-mode "reftex" "RefTeX Minor Mode" t)
(autoload 'turn-on-reftex "reftex" "RefTeX Minor Mode" nil)
(autoload 'reftex-label "reftex-label" "Make label" nil)
(autoload 'reftex-reference "reftex-reference" "Make label" nil)
(autoload 'reftex-citation "reftex-cite" "Make citation" nil)
(autoload 'reftex-index-phrase-mode "reftex-index" "Phrase Mode" t)
(add-hook 'latex-mode-hook 'turn-on-reftex) ; with Emacs latex mode
(add-hook 'reftex-load-hook 'imenu-add-menubar-index)
(add-hook 'LaTeX-mode-hook 'turn-on-reftex)
(setq LaTeX-eqnarray-label "eq"
 LaTeX-equation-label "eq"
 LaTeX-figure-label "fig"
LaTeX-table-label "tab"
LaTeX-myChapter-label "chap"
TeX-auto-save t
TeX-newline-function 'reindent-then-newline-and-indent
TeX-parse-self t
TeX-style-path
'("style/" "auto/"
"/usr/share/emacs21/site-lisp/auctex/style/"
"/var/lib/auctex/emacs21/"
"/usr/local/share/emacs/site-lisp/auctex/style/")
LaTeX-section-hook
'(LaTeX-section-heading
LaTeX-section-title
LaTeX-section-toc
LaTeX-section-section
LaTeX-section-label))
(eval-after-load
   "latex"
 '(TeX-add-style-hook
   "cleveref"
   (lambda ()
     (if (boundp 'reftex-ref-style-alist)
         (add-to-list
          'reftex-ref-style-alist
          '("Cleveref" "cleveref"
            (("\\cref" ?c) ("\\Cref" ?C) ("\\cpageref" ?d) ("\\Cpageref" ?D)))))
     (add-to-list 'reftex-ref-style-default-list "Cleveref")
     (TeX-add-symbols
      '("cref" TeX-arg-ref)
      '("Cref" TeX-arg-ref)
      '("cpageref" TeX-arg-ref)
      '("Cpageref" TeX-arg-ref)))))
;; NOTE: the following lines are commented out:
;; (add-to-list 'load-path "/home/msalem/.emacs.d/predictive")
;; (add-to-list 'load-path "/home/msalem/.emacs.d/predictive/latex")
;; (add-to-list 'load-path "/home/msalem/.emacs.d/predictive/texinfo")
;; (add-to-list 'load-path "/home/msalem/.emacs.d/predictive/misc")
;; (add-to-list 'load-path "/home/msalem/.emacs.d/predictive/html")
;; (require 'predictive)
;; (setq predictive-main-dict 'rpg-dictionary
;;      predictive-auto-learn t
;;      predictive-add-to-dict-ask nil
;;      predictive-use-auto-learn-cache nil
;;      predictive-which-dict t)

(custom-set-variables
 ;; custom-set-variables was added by Custom.
 ;; If you edit it by hand, you could mess it up, so be careful.
 ;; Your init file should contain only one such instance.
 ;; If there is more than one, they won't work right.
'(TeX-source-correlate-method (quote synctex))
'(TeX-source-correlate-start-server t)
'(TeX-view-program-list (quote (("Okular" "okular -unique %o#src:%n%b"))))
'(TeX-view-program-selection (quote ((output-pdf "Okular") ((output-dvi style-pstricks) "dvips and gv") (output-dvi "xdvi") (output-pdf "Evince") (output-html "xdg-open"))))
'(inhibit-startup-screen t))
;(custom-set-faces <-- COMMENTED; otherwise file won't load properly
 ;; custom-set-faces was added by Custom.
 ;; If you edit it by hand, you could mess it up, so be careful.
 ;; Your init file should contain only one such instance.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;







;;
;;  BibTex Mode
;;
;; >>>> Set the default location for your main .bib database here <<<<
;(setq reftex-default-bibliography '("~/git/lab/wjd/latex_wjd/bibtex/bibfiles/wjd.bib"))
(setq auto-mode-alist
      (cons '("\\.bib$" . bibtex-mode) auto-mode-alist))
(add-hook 'bibtex-mode-hook 'turn-on-font-lock)

;;
;;  Markdown Mode
;;
(setq auto-mode-alist (append (list '("\\.md$" . markdown-mode)
                                    '("\\.markdown$" . markdown-mode))
                              auto-mode-alist))
(add-hook 'markdown-mode-hook (lambda ()
                           ; I've made peace with long lines.
      ; (auto-fill-mode 1) ; If you haven't, then uncomment this line.
				))

(custom-set-variables
 ;; custom-set-variables was added by Custom.
 ;; If you edit it by hand, you could mess it up, so be careful.
 ;; Your init file should contain only one such instance.
 ;; If there is more than one, they won't work right.
 '(ansi-color-names-vector ["black" "#d55e00" "#009e73" "#f8ec59" "#0072b2" "#cc79a7" "#56b4e9" "white"])
 '(case-replace nil)
 '(text-scale-mode-step 1.05)
 '(column-number-mode t)
 '(fill-column 80)
 '(font-lock-maximum-decoration t)
 '(fringe-mode 1 nil (fringe))
 '(gutter-buffers-tab-visible-p nil)
 '(paren-mode (quote paren) nil (paren))
 '(scrollbars-visible-p nil)
 '(tool-bar-mode nil)
 '(toolbar-visible-p nil)
 '(unshifted-motion-keys-deselect-region nil)
 '(package-selected-packages
   (quote
    (latex-pretty-symbols zenburn-theme zenburn unicode-math-input unicode-input unicode-fonts unicode-escape org-journal markdown-mode magit latex-unicode-math-mode intero heroku-theme hc-zenburn-theme flatland-theme company-math)))
 '(smartparens-mode nil)
 '(electric-indent-mode nil)

)


;; AGDA ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(setq load-path (cons "~/git/lab/wjd/UF-Agda_wjd/agda/.cabal-sandbox/bin" load-path))

(setenv "LD_LIBRARY_PATH"
  (let ((current (getenv "LD_LIBRARY_PATH"))
        (new "/usr/local/lib:~/git/lab/wjd/UF-Agda_wjd/agda/.cabal-sandbox/bin"))
    (if current (concat new ":" current) new)))

(load-file (let ((coding-system-for-read 'utf-8))
                (shell-command-to-string "agda-mode locate")))

(setq auto-mode-alist
   (append
     '(("\\.agda\\'" . agda2-mode)
       ("\\.lagda.md\\'" . agda2-mode))
     auto-mode-alist))

;; '(agda2-include-dirs (quote ("." "~/git/lab/ualib/ualib.gitlab.io/UALib")))

(add-hook 'agda2-mode-hook (lambda ()
;       (require 'indent-hint)
       (setq smartparens-mode nil)
       (setq electric-indent-mode nil) ) )

(add-hook 'latex-mode-hook (lambda ()
       (setq smartparens-mode nil)
       (setq electric-indent-mode nil) ) )

