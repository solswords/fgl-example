


;; note: these five events could be replaced by
;; (include-book "../../fgl/top" :dir :system)
;; but we do this instead to avoid loading bitops-primitives.
(include-book "centaur/fgl/top-bare" :dir :system)
(include-book "centaur/fgl/bitops" :dir :system)
(include-book "centaur/fgl/check-primitives" :dir :system)
(include-book "centaur/fgl/sat-binder" :dir :system)
#!fgl (install-fgl-metafns example)


(include-book "std/strings/hexify" :dir :system)
(value-triple (tshell-ensure))
(local (include-book "centaur/bitops/ihsext-basics" :dir :system))
(local (include-book "centaur/aignet/transforms" :dir :system))
(local (include-book "centaur/ipasir/ipasir-backend" :dir :system))

(in-package "FGL")



(defun my-fgl-satlink-config ()
  (declare (xargs :guard t))
  (satlink::change-config satlink::*default-config*
                          :cmdline "glucose -model"
                          :verbose nil))

(defmacro nth-bit (n x)
  `(acl2::logbit ,n ,x))

(defmacro right-shift (n x)
  `(ash ,x (- ,n)))

(defmacro left-shift (n x)
  `(ash ,x ,n))

(defmacro zero-extend (n x)
  `(loghead ,n ,x))

(defmacro bitwise-and (x y)
  `(logand ,x ,y))

(defmacro bitwise-or (x y)
  `(logior ,x ,y))

(defmacro bitwise-not (x)
  `(lognot ,x))

(defun synt-int-endp (x)
  (fgl-object-case x
    :g-integer (atom (cdr x.bits))
    :g-concrete (or (not (integerp x.val))
                    (eql x.val 0)
                    (eql x.val -1))
    :otherwise nil))

;; Syntax-bind formulation:
(defmacro int-endp-check (var x)
  `(let ((x ,x))
     (and (syntax-bind ,var (synt-int-endp x))
          (int-endp x))))

;; Binder formulation with binder meta rule (alias built-in check-int-endp) --
;; to use, replace int-endp-check with int-endp-check2 below the bottommost line
;; containing "int-endp-check-replacment-start":
(defmacro int-endp-check2 (var x)
  `(check-int-endp ,var ,x))

;; Binder formulation with binder rewrite rule:
;; to use, replace int-endp-check with int-endp-check3 below the bottommost line
;; containing "int-endp-check-replacment-start":
(defun int-endp-check3 (var x)
  (and (int-endp x) var t))

(def-fgl-brewrite int-endp-check3-binder
  (implies (equal var (and (syntax-bind synchk (synt-int-endp x))
                           (int-endp x)))
           (equal (int-endp-check3 var x) var)))

;;----------- int-endp-check-replacment-start -----------------

(def-fgl-rewrite zero-extend-const-width
  (implies (syntaxp (integerp n))
           (equal (zero-extend n x)
                  (if (or (not (integerp n))
                          (<= n 0))
                      0
                    (intcons (intcar x)
                             (zero-extend (1- n) (intcdr x))))))
  :hints (("goal" :use ((:instance loghead-const-width))
           :in-theory (enable bitops::logbitp**
                              ;; bitops::loghead**
                              bitops::logtail**
                              int-endp))))

(remove-fgl-rewrite loghead-const-width)

(local (defthm logcar/cdr-non-integer
         (implies (not (integerp x))
                  (and (equal (logcar x) 0)
                       (equal (logcdr x) 0)))
         :hints(("Goal" :in-theory (enable logcar logcdr)))))


(def-fgl-rewrite fgl-bitwise-and
  (equal (bitwise-and x y)
         (if (int-endp-check x-endp x)
             (if (intcar x) (ifix y) 0)
           (if (int-endp-check y-endp y)
               (if (intcar y) (ifix x) 0)
             (intcons (and (intcar x)
                           (intcar y))
                      (bitwise-and (intcdr x) (intcdr y))))))
  :hints(("Goal" :in-theory (enable bitops::logand** int-endp))))

(remove-fgl-rewrite fgl-logand)

(defun +c (c x y)
  (+ (bool->bit c)
     (ifix x)
     (ifix y)))

(disable-definition +c)

(def-fgl-rewrite fgl-+c
  (equal (+c c x y)
         (intcons (xor c (xor (intcar x) (intcar y)))
                  (if (and (int-endp-check x-endp x)
                           (int-endp-check y-endp y))
                      (endint (if c
                                  (and (intcar x) (intcar y))
                                (or (intcar x) (intcar y))))
                    (+c (if c
                            (or (intcar x) (intcar y))
                          (and (intcar x) (intcar y)))
                        (intcdr x)
                        (intcdr y)))))
  :hints(("Goal" :in-theory (enable +c int-endp if*
                                    bitops::equal-logcons-strong
                                    bitops::logxor** b-not))))

(def-fgl-rewrite +-to-+c
  (implies (and (integerp x) (integerp y))
           (equal (+ x y) (+c nil x y))))

(remove-fgl-rewrite +-to-+carry)

(def-fgl-rewrite minus-to-+c
  (implies (integerp x)
           (equal (- x) (+c t 0 (lognot x))))
  :hints(("Goal" :in-theory (enable lognot))))

(defun count-bits (x)
  (declare (xargs :guard (natp x)
                  :measure (integer-length (nfix x))
                  :hints (("goal" :expand ((integer-length x))))))
  (if (or (not (integerp x)) (<= x 0))
      0
    (+ (nth-bit 0 x)
       (count-bits (right-shift 1 x)))))

;; (def-fgl-primitive binary-+ (x y)
;;   (b* (((unless (and (gobj-syntactic-integerp x)
;;                      (gobj-syntactic-integerp y)))
;;         ;; Unless x and y are both symbolic or concrete integers, we
;;         ;; fail to apply this rule.  MV stands for Multiple Values
;;         (mv nil nil interp-st))
;;        ;; Extract the list of Boolean formulas for the bits of x and y
;;        (x-bits (gobj-syntactic-integer->bits x))
;;        (y-bits (gobj-syntactic-integer->bits y)))
;;     (stobj-let
;;      ;; Extract the AIG manager object from the interpreter state
;;      ((logicman (interp-st->logicman interp-st)))
;;      ;; return values of the form below
;;      (ans-bits logicman)
;;      ;; add the Boolean formulas for the bits of the sum of x and y to
;;      ;; the AIG.
;;      ;; Return (1) the list of those bits and
;;      ;;        (2) the new AIG manager object
;;      (bfr-+-ss nil x-bits y-bits logicman)
;;      ;; Return (1) flag indicating success
;;      ;;        (2) new symbolic integer containing the resulting formulas
;;      ;;        (3) interpreter state containing new AIG manager.
;;      (mv t (mk-g-integer ans-bits) interp-st))))

(defconst *bitcount*
  '((copy 10 0) ;; copy the operand to regs 10 and 11
    (copy 11 0)
    (const 5 #x55555555) ;; set reg 5 to the mask
    (and 10 5)  ;; bitand the operand with the mask
    (const 0 1)   ;; set reg 0 to 1
    (rshift 11 0) ;; right shift the operand by 1
    (and 11 5)  ;; mask the shifted operand
    (add 10 11) ;; sum the two masked operands
    (copy 11 10) ;; duplicate the sum to reg 11

    (const 5 #x33333333) ;; set reg 5 to the new mask
    (and 10 5)  ;; bitand the operand with the mask
    (const 0 2)   ;; set reg 0 to 2
    (rshift 11 0) ;; right shift the operand by 2
    (and 11 5)  ;; mask the shifted operand
    (add 10 11) ;; sum the two masked operands
    (copy 11 10) ;; duplicate the sum to reg 11

    (const 5 #x07070707) ;; set reg 5 to the new mask
    (and 10 5)  ;; bitand the operand with the mask
    (const 0 4)   ;; set reg 0 to 4
    (rshift 11 0) ;; right shift the operand by 4
    (and 11 5)  ;; mask the shifted operand
    (add 10 11) ;; sum the two masked operands
    (copy 11 10) ;; duplicate the sum to reg 11

    (const 0 8)   ;; set reg 0 to 8
    (rshift 11 0) ;; right shift the operand by 8
    (add 10 11) ;; sum the two masked operands
    (copy 11 10) ;; duplicate the sum to reg 11

    (const 0 16)   ;; set reg 0 to 16
    (rshift 11 0) ;; right shift the operand by 16
    (add 10 11) ;; sum the two operands
    (const 0 #x003f)
    (and 10 0)
    (copy 0 10))) ;; move the result to reg 0.


(defconst *bitcount-bug*
  '((copy 10 0) ;; copy the operand to regs 10 and 11
    (copy 11 0)
    (const 5 #x55555555) ;; set reg 0 to the mask
    (and 10 5)  ;; bitand the operand with the mask
    (const 0 1)   ;; set reg 0 to 1
    (rshift 11 0) ;; right shift the operand by 1
    (and 11 5)  ;; mask the shifted operand
    (add 10 11) ;; sum the two masked operands
    (copy 11 10) ;; duplicate the sum to reg 11

    (const 5 #x33333333) ;; set reg 0 to the new mask
    (and 10 5)  ;; bitand the operand with the mask
    (const 0 2)   ;; set reg 0 to 2
    (rshift 11 0) ;; right shift the operand by 2
    (and 11 5)  ;; mask the shifted operand
    (add 10 11) ;; sum the two masked operands
    (copy 11 10) ;; duplicate the sum to reg 11

    (const 5 #x070f0f03) ;; set reg 0 to the new mask
    (and 10 5)  ;; bitand the operand with the mask
    (const 0 4)   ;; set reg 0 to 4
    (rshift 11 0) ;; right shift the operand by 4
    (and 11 5)  ;; mask the shifted operand
    (add 10 11) ;; sum the two masked operands
    (copy 11 10) ;; duplicate the sum to reg 11

    (const 0 8)   ;; set reg 0 to 8
    (rshift 11 0) ;; right shift the operand by 8
    (add 10 11) ;; sum the two masked operands
    (copy 11 10) ;; duplicate the sum to reg 11

    (const 0 16)   ;; set reg 0 to 16
    (rshift 11 0) ;; right shift the operand by 16
    (add 10 11) ;; sum the two operands
    (const 0 #x003f)
    (and 10 0)
    (copy 0 10)))


;; (defstobj st
;;   (regs :type (array (unsigned-byte 32) (16)) :initially 0))

;; (local (defthm u32-listp-when-regsp
;;          (equal (regsp x)
;;                 (acl2::u32-listp x))))

;; (local (in-theory (disable unsigned-byte-p (tau-system))))

(defun get-st-reg (n st)
  (declare (xargs :guard (and (integerp n)
                              (true-listp st))))
  (zero-extend 32 (ifix (nth (zero-extend 4 n) st))))

(defsection get-st-reg
  (defthm natp-of-get-st-reg
    (natp (get-st-reg n st))
    :rule-classes :type-prescription)

  (defthm unsigned-byte-32-of-get-st-reg
    (unsigned-byte-p 32 (get-st-reg n st))))




(defun set-st-reg (n val st)
  (declare (xargs :guard (and (integerp n) (integerp val) (true-listp st))))
  (update-nth (zero-extend 4 n)
              (zero-extend 32 val)
              (mbe :logic (true-list-fix st) :exec st)))

(defthm true-listp-of-set-st-reg
  (true-listp (set-st-reg n val st))
  :rule-classes :type-prescription)

(def-fgl-rewrite get-st-reg-of-set-st-reg
  (equal (get-st-reg i (set-st-reg j v st))
         (if (equal (zero-extend 4 i) (zero-extend 4 j))
             (zero-extend 32 v)
           (get-st-reg i st)))
  :hints(("Goal" :in-theory (enable get-st-reg set-st-reg))))

(in-theory (enable get-st-reg-of-set-st-reg))
(in-theory (disable get-st-reg set-st-reg))

;; (add-fgl-rewrite get-st-reg-of-set-st-reg)

(defun hide-get-st-reg (n st)
  (get-st-reg n st))

(def-fgl-rewrite get-st-reg-generate-bits
  (implies (syntaxp (fgl-object-case st :g-var))
           (equal (get-st-reg n st)
                  (zero-extend 32 (hide-get-st-reg n st))))
  :hints(("Goal" :in-theory (enable get-st-reg))))

(disable-definition get-st-reg)
(disable-definition hide-get-st-reg)
(disable-definition set-st-reg)


(def-ctrex-rule get-st-reg-ctrex-rule
  :match ((val (get-st-reg idx x)))
  :assign (set-st-reg idx val x)
  :assigned-var x
  ;;:hyp (alistp x)
  :ruletype :property)

(def-ctrex-rule hide-get-st-reg-ctrex-rule
  :match ((val (hide-get-st-reg idx x)))
  :assign (set-st-reg idx val x)
  :assigned-var x
  :ruletype :property)

(def-ctrex-rule equal-get-st-reg-ctrex-rule
  :match ((ans (equal (get-st-reg idx x) val)))
  :assign (if ans (set-st-reg idx val x) x)
  :assigned-var x
  :ruletype :property)



(defun instp (x)
  (declare (xargs :guard t))
  (case-match x
    (('const x y) (and (unsigned-byte-p 4 x) (unsigned-byte-p 32 y)))
    (('copy x y)  (and (unsigned-byte-p 4 x) (unsigned-byte-p 4 y)))
    (('add x y) (and (unsigned-byte-p 4 x) (unsigned-byte-p 4 y)))
    (('and x y) (and (unsigned-byte-p 4 x) (unsigned-byte-p 4 y)))
    ;; (('not x)   (unsigned-byte-p 4 x))
    (('rshift x y) (and (unsigned-byte-p 4 x) (unsigned-byte-p 4 y)))
    (& nil)))

(defun run-inst (inst st)
  (declare (xargs :guard (and (instp inst)
                              (true-listp st))))
  (let* ((instname (first inst))
         (args (rest inst))
         (x (first args))
         (y (second args))
         (ans (case instname
                (const     y)
                (copy      (get-st-reg y st))
                (add       (+ (get-st-reg x st)
                              (get-st-reg y st)))
                (and       (bitwise-and (get-st-reg x st)
                                        (get-st-reg y st)))
                ;; (not       (bitwise-not (get-st-reg x st)))
                (rshift    (right-shift (get-st-reg y st)
                                        (get-st-reg x st))))))
    (set-st-reg x ans st)))

(std::deflist inst-listp (x)
  (instp x))

(defun run-prog (insts st)
  (declare (xargs :guard (and (inst-listp insts)
                              (true-listp st))))
  (if (atom insts)
      st
    (let ((st (run-inst (first insts) st)))
      (run-prog (rest insts) st))))

(defun run-count-bits (x st)
  (declare (xargs :guard (and (integerp x)
                              (true-listp st))))
  (let* ((st (set-st-reg 0 x st))
         (st (run-prog *bitcount* st))
         (ans (get-st-reg 0 st)))
    (mv ans st)))
       

(local (in-theory (disable w)))


    
(def-fgl-thm bitcount-implements-count-bits
  (let* ((input (get-st-reg 0 st))
         (final-st (run-prog *bitcount* st))
         (result (get-st-reg 0 final-st)))
    (equal result (count-bits input))))

(make-event
 '(:or (with-output :off (error prove summary)
         (def-fgl-thm bitcount-implements-count-bits-bug
           (let* ((input (get-st-reg 0 st))
                  (final-st (run-prog *bitcount-bug* st))
                  (result (get-st-reg 0 final-st))
                  (spec (count-bits input)))
             (progn$
              (cw "input:  ~s0~%" (str::hexify input))
              (cw "result: ~s0~%" (str::hexify result))
              (cw "spec:   ~s0~%" (str::hexify spec))
              (equal result spec)))
           :prof-enabledp nil))
   (value-triple "bugged program correctly failed to prove")))



                                        
(defmacro output (&rest args) (cons 'cw (cons (concatenate 'string (car args) "~%") (cdr args))))

(defun incr-sat-config ()
  (make-fgl-ipasir-config :ignore-pathcond nil))

(defun mono-sat-config ()
  (make-fgl-satlink-monolithic-sat-config))

(set-ignore-ok t)

(def-fgl-program minimize-counterexample
  (curr-bit irrel-bits-mask goal
            input-vec ctrex-val input-vec-nbits)
  (if (equal curr-bit input-vec-nbits)
      irrel-bits-mask
    (let* ((next-irrel-bits
            (bitwise-or (left-shift curr-bit 1)
                        irrel-bits-mask))
           (not-irrel (bitwise-not next-irrel-bits))
           (equal-except-on-irrel
            (equal (bitwise-and input-vec not-irrel)
                   (bitwise-and ctrex-val not-irrel)))
           (goal-sat (fgl-sat-check
                      (incr-sat-config)
                      (and equal-except-on-irrel
                           goal)))
           (irrel? (syntax-interp (eq goal-sat nil)))
           (ignore
            (if irrel?
                (output "Bit ~x0 is irrelevant" curr-bit)
              (output "Bit ~x0 is relevant" curr-bit)))
           (irrel-bits-mask
            (if irrel? next-irrel-bits irrel-bits-mask)))
      (minimize-counterexample (+ 1 curr-bit)
                               irrel-bits-mask
                               goal
                               input-vec
                               ctrex-val
                               input-vec-nbits))))
  

(define interp-st-store-error (prefix err interp-st)
  (if err
      (let ((msg (msg "~s0 ~@1" prefix err)))
        (prog2$ (output "~@0" msg)
                (fgl-interp-store-debug-info msg nil interp-st)))
    interp-st))


(def-fgl-program fetch-counterexample-value (goal input-vec)
  (let* ((check (fgl-validity-check (mono-sat-config) goal)))
    (declare (ignore check))
    (syntax-interp
     (b* (((mv err ?ist) (interp-st-sat-counterexample (mono-sat-config) interp-st state))
          (?interp-st (interp-st-store-error "SAT counterexample error:" err interp-st))
          ((mv err ?bindings-vals ?var-vals ?interp-st)
           (interp-st-counterex-bindings (list (cons 'input-vec input-vec))
                                         interp-st state))
          (?interp-st (interp-st-store-error "Counterex-bindings error:" err interp-st)))
       (g-concrete (cdr (assoc 'input-vec bindings-vals)))))))


(define output-val (prefix val)
  (cw "~s0 ~s1~%" prefix (str::hexify val)))

(make-event
 '(:or (with-output :off (error prove summary)
         (def-fgl-thm bitcount-implements-count-bits-analyze
           (let* ((input (get-st-reg 0 st))
                  (final-st (run-prog *bitcount-bug* st))
                  (result (get-st-reg 0 final-st))
                  (spec (count-bits input))
                  (goal (equal result spec)))
             (fgl-prog2
              (let* ((ctrex-val (fetch-counterexample-value
                                 goal input))
                     (irrel-bits (minimize-counterexample
                                  0 0 goal input ctrex-val 32)))
                (fgl-prog2
                 (output-val "Counterexample value:" ctrex-val)
                 (output-val "Irrelevant mask:     " irrel-bits)))
              goal))
           :skip-toplevel-sat-check t
           :prof-enabledp nil
           ))
   (value-triple "bugged program correctly failed to prove, see above for irrelevant mask")))
