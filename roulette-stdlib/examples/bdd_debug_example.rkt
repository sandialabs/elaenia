#lang roulette/example/disrupt

(require (submod roulette/engine/rsdd gui))

(debug (and (flip 1/2) (flip 1/3)))

(require pict pict-abbrevs)

; assuming x is your pict
; keep in mind the path string is relative to where you're running the
; racket program from, so if the racket program is in "~", you'll end
; up with "~/image_name.png"
;(save-pict "image_name.png" x 'png)
