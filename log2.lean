import ACL2Lean.Logic
open ACL2

partial def flog2 (n : SExpr) : SExpr :=
  (Logic.if_ (Logic.zp n) (SExpr.atom (.number (.int (0)))) (Logic.if_ (Logic.evenp n) (Logic.plus (SExpr.atom (.number (.int (1)))) (flog2 (Logic.div n (SExpr.atom (.number (.int (2))))))) (flog2 (Logic.minus n (SExpr.atom (.number (.int (1))))))))

theorem flog2_is_correct (n : SExpr) : Logic.toBool ((Logic.implies (Logic.posp n) (Logic.and (Logic.le (Logic.expt (SExpr.atom (.number (.int (2)))) (flog2 n)) n) (Logic.lt n (Logic.expt (SExpr.atom (.number (.int (2)))) (Logic.plus (SExpr.atom (.number (.int (1)))) (flog2 n))))))) = true :=
  sorry

partial def clog2 (n : SExpr) : SExpr :=
  (Logic.if_ (Logic.zp n) (SExpr.atom (.number (.int (-1)))) (Logic.if_ (Logic.eq n (SExpr.atom (.number (.int (1))))) (SExpr.atom (.number (.int (0)))) (Logic.if_ (Logic.evenp n) (Logic.plus (SExpr.atom (.number (.int (1)))) (clog2 (Logic.div n (SExpr.atom (.number (.int (2))))))) (Logic.plus (SExpr.atom (.number (.int (1)))) (clog2 (Logic.div (Logic.plus (SExpr.atom (.number (.int (1)))) n) (SExpr.atom (.number (.int (2))))))))))

theorem natp_clog2 (n : SExpr) : Logic.toBool ((Logic.implies (Logic.and (Logic.integerp n) (Logic.gt n (SExpr.atom (.number (.int (0)))))) (Logic.ge (clog2 n) (SExpr.atom (.number (.int (0))))))) = true := /- hints: ACL2.SExpr.cons
  (ACL2.SExpr.atom (ACL2.Atom.keyword "rule-classes"))
  (ACL2.SExpr.cons (ACL2.SExpr.atom (ACL2.Atom.keyword "type-prescription")) (ACL2.SExpr.nil)) -/
  sorry

theorem posp_1_div_2_plus_1_div_2_times_n (n : SExpr) : Logic.toBool ((Logic.implies (Logic.and (Logic.integerp n) (Logic.and (Logic.not (Logic.integerp (Logic.times (SExpr.atom (.number (.rational (1) (2)))) n))) (Logic.gt n (SExpr.atom (.number (.int (1))))))) (Logic.and (Logic.integerp (Logic.plus (SExpr.atom (.number (.rational (1) (2)))) (Logic.times (SExpr.atom (.number (.rational (1) (2)))) n))) (Logic.gt (Logic.plus (SExpr.atom (.number (.rational (1) (2)))) (Logic.times (SExpr.atom (.number (.rational (1) (2)))) n)) (SExpr.atom (.number (.int (0)))))))) = true := /- hints: ACL2.SExpr.cons
  (ACL2.SExpr.atom (ACL2.Atom.keyword "rule-classes"))
  (ACL2.SExpr.cons (ACL2.SExpr.atom (ACL2.Atom.keyword "type-prescription")) (ACL2.SExpr.nil)) -/
  sorry

theorem posp_clog2 (n : SExpr) : Logic.toBool ((Logic.implies (Logic.and (Logic.integerp n) (Logic.gt n (SExpr.atom (.number (.int (1)))))) (Logic.gt (clog2 n) (SExpr.atom (.number (.int (0))))))) = true := /- hints: ACL2.SExpr.cons
  (ACL2.SExpr.atom (ACL2.Atom.keyword "rule-classes"))
  (ACL2.SExpr.cons (ACL2.SExpr.atom (ACL2.Atom.keyword "type-prescription")) (ACL2.SExpr.nil)) -/
  sorry

theorem clog2_lemma_a (n : SExpr) : Logic.toBool ((Logic.implies (Logic.and (Logic.not (Logic.equal n (SExpr.atom (.number (.int (1)))))) (Logic.and (Logic.not (Logic.integerp (Logic.times (SExpr.atom (.number (.rational (1) (2)))) n))) (Logic.and (Logic.lt (Logic.expt (SExpr.atom (.number (.int (2)))) (Logic.plus (SExpr.atom (.number (.int (-1)))) (clog2 (Logic.plus (SExpr.atom (.number (.rational (1) (2)))) (Logic.times (SExpr.atom (.number (.rational (1) (2)))) n))))) (Logic.plus (SExpr.atom (.number (.rational (1) (2)))) (Logic.times (SExpr.atom (.number (.rational (1) (2)))) n))) (Logic.and (Logic.integerp n) (Logic.lt (SExpr.atom (.number (.int (0)))) n))))) (Logic.lt (Logic.expt (SExpr.atom (.number (.int (2)))) (clog2 (Logic.plus (SExpr.atom (.number (.rational (1) (2)))) (Logic.times (SExpr.atom (.number (.rational (1) (2)))) n)))) (Logic.plus (SExpr.atom (.number (.int (1)))) n)))) = true := /- hints: ACL2.SExpr.cons
  (ACL2.SExpr.atom (ACL2.Atom.keyword "hints"))
  (ACL2.SExpr.cons
    (ACL2.SExpr.cons
      (ACL2.SExpr.cons
        (ACL2.SExpr.atom (ACL2.Atom.string "goal"))
        (ACL2.SExpr.cons
          (ACL2.SExpr.atom (ACL2.Atom.keyword "use"))
          (ACL2.SExpr.cons
            (ACL2.SExpr.cons
              (ACL2.SExpr.atom (ACL2.Atom.keyword "instance"))
              (ACL2.SExpr.cons
                (ACL2.SExpr.cons
                  (ACL2.SExpr.atom (ACL2.Atom.keyword "theorem"))
                  (ACL2.SExpr.cons
                    (ACL2.SExpr.cons
                      (ACL2.SExpr.atom (ACL2.Atom.symbol { package := "ACL2", name := "implies" }))
                      (ACL2.SExpr.cons
                        (ACL2.SExpr.cons
                          (ACL2.SExpr.atom (ACL2.Atom.symbol { package := "ACL2", name := "<" }))
                          (ACL2.SExpr.cons
                            (ACL2.SExpr.atom (ACL2.Atom.symbol { package := "ACL2", name := "x" }))
                            (ACL2.SExpr.cons
                              (ACL2.SExpr.atom (ACL2.Atom.symbol { package := "ACL2", name := "y" }))
                              (ACL2.SExpr.nil))))
                        (ACL2.SExpr.cons
                          (ACL2.SExpr.cons
                            (ACL2.SExpr.atom (ACL2.Atom.symbol { package := "ACL2", name := "<" }))
                            (ACL2.SExpr.cons
                              (ACL2.SExpr.cons
                                (ACL2.SExpr.atom (ACL2.Atom.symbol { package := "ACL2", name := "*" }))
                                (ACL2.SExpr.cons
                                  (ACL2.SExpr.atom (ACL2.Atom.number (ACL2.Number.int 2)))
                                  (ACL2.SExpr.cons
                                    (ACL2.SExpr.atom (ACL2.Atom.symbol { package := "ACL2", name := "x" }))
                                    (ACL2.SExpr.nil))))
                              (ACL2.SExpr.cons
                                (ACL2.SExpr.cons
                                  (ACL2.SExpr.atom (ACL2.Atom.symbol { package := "ACL2", name := "*" }))
                                  (ACL2.SExpr.cons
                                    (ACL2.SExpr.atom (ACL2.Atom.number (ACL2.Number.int 2)))
                                    (ACL2.SExpr.cons
                                      (ACL2.SExpr.atom (ACL2.Atom.symbol { package := "ACL2", name := "y" }))
                                      (ACL2.SExpr.nil))))
                                (ACL2.SExpr.nil))))
                          (ACL2.SExpr.nil))))
                    (ACL2.SExpr.nil)))
                (ACL2.SExpr.cons
                  (ACL2.SExpr.cons
                    (ACL2.SExpr.atom (ACL2.Atom.symbol { package := "ACL2", name := "x" }))
                    (ACL2.SExpr.cons
                      (ACL2.SExpr.cons
                        (ACL2.SExpr.atom (ACL2.Atom.symbol { package := "ACL2", name := "expt" }))
                        (ACL2.SExpr.cons
                          (ACL2.SExpr.atom (ACL2.Atom.number (ACL2.Number.int 2)))
                          (ACL2.SExpr.cons
                            (ACL2.SExpr.cons
                              (ACL2.SExpr.atom (ACL2.Atom.symbol { package := "ACL2", name := "+" }))
                              (ACL2.SExpr.cons
                                (ACL2.SExpr.atom (ACL2.Atom.number (ACL2.Number.int (-1))))
                                (ACL2.SExpr.cons
                                  (ACL2.SExpr.cons
                                    (ACL2.SExpr.atom (ACL2.Atom.symbol { package := "ACL2", name := "clog2" }))
                                    (ACL2.SExpr.cons
                                      (ACL2.SExpr.cons
                                        (ACL2.SExpr.atom (ACL2.Atom.symbol { package := "ACL2", name := "+" }))
                                        (ACL2.SExpr.cons
                                          (ACL2.SExpr.atom (ACL2.Atom.number (ACL2.Number.rational 1 2)))
                                          (ACL2.SExpr.cons
                                            (ACL2.SExpr.cons
                                              (ACL2.SExpr.atom (ACL2.Atom.symbol { package := "ACL2", name := "*" }))
                                              (ACL2.SExpr.cons
                                                (ACL2.SExpr.atom (ACL2.Atom.number (ACL2.Number.rational 1 2)))
                                                (ACL2.SExpr.cons
                                                  (ACL2.SExpr.atom
                                                    (ACL2.Atom.symbol { package := "ACL2", name := "n" }))
                                                  (ACL2.SExpr.nil))))
                                            (ACL2.SExpr.nil))))
                                      (ACL2.SExpr.nil)))
                                  (ACL2.SExpr.nil))))
                            (ACL2.SExpr.nil))))
                      (ACL2.SExpr.nil)))
                  (ACL2.SExpr.cons
                    (ACL2.SExpr.cons
                      (ACL2.SExpr.atom (ACL2.Atom.symbol { package := "ACL2", name := "y" }))
                      (ACL2.SExpr.cons
                        (ACL2.SExpr.cons
                          (ACL2.SExpr.atom (ACL2.Atom.symbol { package := "ACL2", name := "+" }))
                          (ACL2.SExpr.cons
                            (ACL2.SExpr.atom (ACL2.Atom.number (ACL2.Number.rational 1 2)))
                            (ACL2.SExpr.cons
                              (ACL2.SExpr.cons
                                (ACL2.SExpr.atom (ACL2.Atom.symbol { package := "ACL2", name := "*" }))
                                (ACL2.SExpr.cons
                                  (ACL2.SExpr.atom (ACL2.Atom.number (ACL2.Number.rational 1 2)))
                                  (ACL2.SExpr.cons
                                    (ACL2.SExpr.atom (ACL2.Atom.symbol { package := "ACL2", name := "n" }))
                                    (ACL2.SExpr.nil))))
                              (ACL2.SExpr.nil))))
                        (ACL2.SExpr.nil)))
                    (ACL2.SExpr.nil)))))
            (ACL2.SExpr.nil))))
      (ACL2.SExpr.nil))
    (ACL2.SExpr.nil)) -/
  sorry

theorem clog2_lemma_b (n : SExpr) : Logic.toBool ((Logic.implies (Logic.and (Logic.not (Logic.equal n (SExpr.atom (.number (.int (1)))))) (Logic.and (Logic.not (Logic.integerp (Logic.times (SExpr.atom (.number (.rational (1) (2)))) n))) (Logic.and (Logic.lt (Logic.expt (SExpr.atom (.number (.int (2)))) (Logic.plus (SExpr.atom (.number (.int (-1)))) (clog2 (Logic.plus (SExpr.atom (.number (.rational (1) (2)))) (Logic.times (SExpr.atom (.number (.rational (1) (2)))) n))))) (Logic.plus (SExpr.atom (.number (.rational (1) (2)))) (Logic.times (SExpr.atom (.number (.rational (1) (2)))) n))) (Logic.and (Logic.integerp n) (Logic.lt (SExpr.atom (.number (.int (0)))) n))))) (Logic.lt (Logic.expt (SExpr.atom (.number (.int (2)))) (clog2 (Logic.plus (SExpr.atom (.number (.rational (1) (2)))) (Logic.times (SExpr.atom (.number (.rational (1) (2)))) n)))) n))) = true := /- hints: ACL2.SExpr.cons
  (ACL2.SExpr.atom (ACL2.Atom.keyword "hints"))
  (ACL2.SExpr.cons
    (ACL2.SExpr.cons
      (ACL2.SExpr.cons
        (ACL2.SExpr.atom (ACL2.Atom.string "goal"))
        (ACL2.SExpr.cons
          (ACL2.SExpr.atom (ACL2.Atom.keyword "use"))
          (ACL2.SExpr.cons
            (ACL2.SExpr.cons
              (ACL2.SExpr.atom (ACL2.Atom.keyword "instance"))
              (ACL2.SExpr.cons
                (ACL2.SExpr.cons
                  (ACL2.SExpr.atom (ACL2.Atom.keyword "theorem"))
                  (ACL2.SExpr.cons
                    (ACL2.SExpr.cons
                      (ACL2.SExpr.atom (ACL2.Atom.symbol { package := "ACL2", name := "implies" }))
                      (ACL2.SExpr.cons
                        (ACL2.SExpr.cons
                          (ACL2.SExpr.atom (ACL2.Atom.symbol { package := "ACL2", name := "and" }))
                          (ACL2.SExpr.cons
                            (ACL2.SExpr.cons
                              (ACL2.SExpr.atom (ACL2.Atom.symbol { package := "ACL2", name := "integerp" }))
                              (ACL2.SExpr.cons
                                (ACL2.SExpr.atom (ACL2.Atom.symbol { package := "ACL2", name := "i" }))
                                (ACL2.SExpr.nil)))
                            (ACL2.SExpr.cons
                              (ACL2.SExpr.cons
                                (ACL2.SExpr.atom (ACL2.Atom.symbol { package := "ACL2", name := "integerp" }))
                                (ACL2.SExpr.cons
                                  (ACL2.SExpr.atom (ACL2.Atom.symbol { package := "ACL2", name := "j" }))
                                  (ACL2.SExpr.nil)))
                              (ACL2.SExpr.cons
                                (ACL2.SExpr.cons
                                  (ACL2.SExpr.atom (ACL2.Atom.symbol { package := "ACL2", name := "evenp" }))
                                  (ACL2.SExpr.cons
                                    (ACL2.SExpr.atom (ACL2.Atom.symbol { package := "ACL2", name := "i" }))
                                    (ACL2.SExpr.nil)))
                                (ACL2.SExpr.cons
                                  (ACL2.SExpr.cons
                                    (ACL2.SExpr.atom (ACL2.Atom.symbol { package := "ACL2", name := "oddp" }))
                                    (ACL2.SExpr.cons
                                      (ACL2.SExpr.atom (ACL2.Atom.symbol { package := "ACL2", name := "j" }))
                                      (ACL2.SExpr.nil)))
                                  (ACL2.SExpr.cons
                                    (ACL2.SExpr.cons
                                      (ACL2.SExpr.atom (ACL2.Atom.symbol { package := "ACL2", name := "<" }))
                                      (ACL2.SExpr.cons
                                        (ACL2.SExpr.atom (ACL2.Atom.symbol { package := "ACL2", name := "i" }))
                                        (ACL2.SExpr.cons
                                          (ACL2.SExpr.cons
                                            (ACL2.SExpr.atom (ACL2.Atom.symbol { package := "ACL2", name := "+" }))
                                            (ACL2.SExpr.cons
                                              (ACL2.SExpr.atom (ACL2.Atom.number (ACL2.Number.int 1)))
                                              (ACL2.SExpr.cons
                                                (ACL2.SExpr.atom (ACL2.Atom.symbol { package := "ACL2", name := "j" }))
                                                (ACL2.SExpr.nil))))
                                          (ACL2.SExpr.nil))))
                                    (ACL2.SExpr.nil)))))))
                        (ACL2.SExpr.cons
                          (ACL2.SExpr.cons
                            (ACL2.SExpr.atom (ACL2.Atom.symbol { package := "ACL2", name := "<" }))
                            (ACL2.SExpr.cons
                              (ACL2.SExpr.atom (ACL2.Atom.symbol { package := "ACL2", name := "i" }))
                              (ACL2.SExpr.cons
                                (ACL2.SExpr.atom (ACL2.Atom.symbol { package := "ACL2", name := "j" }))
                                (ACL2.SExpr.nil))))
                          (ACL2.SExpr.nil))))
                    (ACL2.SExpr.nil)))
                (ACL2.SExpr.cons
                  (ACL2.SExpr.cons
                    (ACL2.SExpr.atom (ACL2.Atom.symbol { package := "ACL2", name := "i" }))
                    (ACL2.SExpr.cons
                      (ACL2.SExpr.cons
                        (ACL2.SExpr.atom (ACL2.Atom.symbol { package := "ACL2", name := "expt" }))
                        (ACL2.SExpr.cons
                          (ACL2.SExpr.atom (ACL2.Atom.number (ACL2.Number.int 2)))
                          (ACL2.SExpr.cons
                            (ACL2.SExpr.cons
                              (ACL2.SExpr.atom (ACL2.Atom.symbol { package := "ACL2", name := "clog2" }))
                              (ACL2.SExpr.cons
                                (ACL2.SExpr.cons
                                  (ACL2.SExpr.atom (ACL2.Atom.symbol { package := "ACL2", name := "+" }))
                                  (ACL2.SExpr.cons
                                    (ACL2.SExpr.atom (ACL2.Atom.number (ACL2.Number.rational 1 2)))
                                    (ACL2.SExpr.cons
                                      (ACL2.SExpr.cons
                                        (ACL2.SExpr.atom (ACL2.Atom.symbol { package := "ACL2", name := "*" }))
                                        (ACL2.SExpr.cons
                                          (ACL2.SExpr.atom (ACL2.Atom.number (ACL2.Number.rational 1 2)))
                                          (ACL2.SExpr.cons
                                            (ACL2.SExpr.atom (ACL2.Atom.symbol { package := "ACL2", name := "n" }))
                                            (ACL2.SExpr.nil))))
                                      (ACL2.SExpr.nil))))
                                (ACL2.SExpr.nil)))
                            (ACL2.SExpr.nil))))
                      (ACL2.SExpr.nil)))
                  (ACL2.SExpr.cons
                    (ACL2.SExpr.cons
                      (ACL2.SExpr.atom (ACL2.Atom.symbol { package := "ACL2", name := "j" }))
                      (ACL2.SExpr.cons
                        (ACL2.SExpr.atom (ACL2.Atom.symbol { package := "ACL2", name := "n" }))
                        (ACL2.SExpr.nil)))
                    (ACL2.SExpr.nil)))))
            (ACL2.SExpr.nil))))
      (ACL2.SExpr.nil))
    (ACL2.SExpr.nil)) -/
  sorry

theorem clog2_is_correct_lower (n : SExpr) : Logic.toBool ((Logic.implies (Logic.posp n) (Logic.lt (Logic.expt (SExpr.atom (.number (.int (2)))) (Logic.plus (SExpr.atom (.number (.int (-1)))) (clog2 n))) n))) = true := /- hints: ACL2.SExpr.cons
  (ACL2.SExpr.atom (ACL2.Atom.keyword "hints"))
  (ACL2.SExpr.cons
    (ACL2.SExpr.cons
      (ACL2.SExpr.cons
        (ACL2.SExpr.atom (ACL2.Atom.string "Subgoal *1/5"))
        (ACL2.SExpr.cons
          (ACL2.SExpr.atom (ACL2.Atom.keyword "use"))
          (ACL2.SExpr.cons
            (ACL2.SExpr.cons
              (ACL2.SExpr.atom (ACL2.Atom.keyword "instance"))
              (ACL2.SExpr.cons
                (ACL2.SExpr.cons
                  (ACL2.SExpr.atom (ACL2.Atom.keyword "theorem"))
                  (ACL2.SExpr.cons
                    (ACL2.SExpr.cons
                      (ACL2.SExpr.atom (ACL2.Atom.symbol { package := "ACL2", name := "implies" }))
                      (ACL2.SExpr.cons
                        (ACL2.SExpr.cons
                          (ACL2.SExpr.atom (ACL2.Atom.symbol { package := "ACL2", name := "<" }))
                          (ACL2.SExpr.cons
                            (ACL2.SExpr.atom (ACL2.Atom.symbol { package := "ACL2", name := "x" }))
                            (ACL2.SExpr.cons
                              (ACL2.SExpr.atom (ACL2.Atom.symbol { package := "ACL2", name := "y" }))
                              (ACL2.SExpr.nil))))
                        (ACL2.SExpr.cons
                          (ACL2.SExpr.cons
                            (ACL2.SExpr.atom (ACL2.Atom.symbol { package := "ACL2", name := "<" }))
                            (ACL2.SExpr.cons
                              (ACL2.SExpr.cons
                                (ACL2.SExpr.atom (ACL2.Atom.symbol { package := "ACL2", name := "*" }))
                                (ACL2.SExpr.cons
                                  (ACL2.SExpr.atom (ACL2.Atom.number (ACL2.Number.int 2)))
                                  (ACL2.SExpr.cons
                                    (ACL2.SExpr.atom (ACL2.Atom.symbol { package := "ACL2", name := "x" }))
                                    (ACL2.SExpr.nil))))
                              (ACL2.SExpr.cons
                                (ACL2.SExpr.cons
                                  (ACL2.SExpr.atom (ACL2.Atom.symbol { package := "ACL2", name := "*" }))
                                  (ACL2.SExpr.cons
                                    (ACL2.SExpr.atom (ACL2.Atom.number (ACL2.Number.int 2)))
                                    (ACL2.SExpr.cons
                                      (ACL2.SExpr.atom (ACL2.Atom.symbol { package := "ACL2", name := "y" }))
                                      (ACL2.SExpr.nil))))
                                (ACL2.SExpr.nil))))
                          (ACL2.SExpr.nil))))
                    (ACL2.SExpr.nil)))
                (ACL2.SExpr.cons
                  (ACL2.SExpr.cons
                    (ACL2.SExpr.atom (ACL2.Atom.symbol { package := "ACL2", name := "x" }))
                    (ACL2.SExpr.cons
                      (ACL2.SExpr.cons
                        (ACL2.SExpr.atom (ACL2.Atom.symbol { package := "ACL2", name := "expt" }))
                        (ACL2.SExpr.cons
                          (ACL2.SExpr.atom (ACL2.Atom.number (ACL2.Number.int 2)))
                          (ACL2.SExpr.cons
                            (ACL2.SExpr.cons
                              (ACL2.SExpr.atom (ACL2.Atom.symbol { package := "ACL2", name := "+" }))
                              (ACL2.SExpr.cons
                                (ACL2.SExpr.atom (ACL2.Atom.number (ACL2.Number.int (-1))))
                                (ACL2.SExpr.cons
                                  (ACL2.SExpr.cons
                                    (ACL2.SExpr.atom (ACL2.Atom.symbol { package := "ACL2", name := "clog2" }))
                                    (ACL2.SExpr.cons
                                      (ACL2.SExpr.cons
                                        (ACL2.SExpr.atom (ACL2.Atom.symbol { package := "ACL2", name := "*" }))
                                        (ACL2.SExpr.cons
                                          (ACL2.SExpr.atom (ACL2.Atom.symbol { package := "ACL2", name := "n" }))
                                          (ACL2.SExpr.cons
                                            (ACL2.SExpr.atom (ACL2.Atom.number (ACL2.Number.rational 1 2)))
                                            (ACL2.SExpr.nil))))
                                      (ACL2.SExpr.nil)))
                                  (ACL2.SExpr.nil))))
                            (ACL2.SExpr.nil))))
                      (ACL2.SExpr.nil)))
                  (ACL2.SExpr.cons
                    (ACL2.SExpr.cons
                      (ACL2.SExpr.atom (ACL2.Atom.symbol { package := "ACL2", name := "y" }))
                      (ACL2.SExpr.cons
                        (ACL2.SExpr.cons
                          (ACL2.SExpr.atom (ACL2.Atom.symbol { package := "ACL2", name := "*" }))
                          (ACL2.SExpr.cons
                            (ACL2.SExpr.atom (ACL2.Atom.number (ACL2.Number.rational 1 2)))
                            (ACL2.SExpr.cons
                              (ACL2.SExpr.atom (ACL2.Atom.symbol { package := "ACL2", name := "n" }))
                              (ACL2.SExpr.nil))))
                        (ACL2.SExpr.nil)))
                    (ACL2.SExpr.nil)))))
            (ACL2.SExpr.nil))))
      (ACL2.SExpr.nil))
    (ACL2.SExpr.nil)) -/
  sorry

theorem clog2_is_correct_upper (n : SExpr) : Logic.toBool ((Logic.implies (Logic.natp n) (Logic.le n (Logic.expt (SExpr.atom (.number (.int (2)))) (clog2 n))))) = true := /- hints: ACL2.SExpr.cons
  (ACL2.SExpr.atom (ACL2.Atom.keyword "hints"))
  (ACL2.SExpr.cons
    (ACL2.SExpr.cons
      (ACL2.SExpr.cons
        (ACL2.SExpr.atom (ACL2.Atom.string "Subgoal *1/8"))
        (ACL2.SExpr.cons
          (ACL2.SExpr.atom (ACL2.Atom.keyword "use"))
          (ACL2.SExpr.cons
            (ACL2.SExpr.cons
              (ACL2.SExpr.atom (ACL2.Atom.keyword "instance"))
              (ACL2.SExpr.cons
                (ACL2.SExpr.cons
                  (ACL2.SExpr.atom (ACL2.Atom.keyword "theorem"))
                  (ACL2.SExpr.cons
                    (ACL2.SExpr.cons
                      (ACL2.SExpr.atom (ACL2.Atom.symbol { package := "ACL2", name := "implies" }))
                      (ACL2.SExpr.cons
                        (ACL2.SExpr.cons
                          (ACL2.SExpr.atom (ACL2.Atom.symbol { package := "ACL2", name := "<=" }))
                          (ACL2.SExpr.cons
                            (ACL2.SExpr.atom (ACL2.Atom.symbol { package := "ACL2", name := "x" }))
                            (ACL2.SExpr.cons
                              (ACL2.SExpr.atom (ACL2.Atom.symbol { package := "ACL2", name := "y" }))
                              (ACL2.SExpr.nil))))
                        (ACL2.SExpr.cons
                          (ACL2.SExpr.cons
                            (ACL2.SExpr.atom (ACL2.Atom.symbol { package := "ACL2", name := "<=" }))
                            (ACL2.SExpr.cons
                              (ACL2.SExpr.cons
                                (ACL2.SExpr.atom (ACL2.Atom.symbol { package := "ACL2", name := "*" }))
                                (ACL2.SExpr.cons
                                  (ACL2.SExpr.atom (ACL2.Atom.number (ACL2.Number.int 2)))
                                  (ACL2.SExpr.cons
                                    (ACL2.SExpr.atom (ACL2.Atom.symbol { package := "ACL2", name := "x" }))
                                    (ACL2.SExpr.nil))))
                              (ACL2.SExpr.cons
                                (ACL2.SExpr.cons
                                  (ACL2.SExpr.atom (ACL2.Atom.symbol { package := "ACL2", name := "*" }))
                                  (ACL2.SExpr.cons
                                    (ACL2.SExpr.atom (ACL2.Atom.number (ACL2.Number.int 2)))
                                    (ACL2.SExpr.cons
                                      (ACL2.SExpr.atom (ACL2.Atom.symbol { package := "ACL2", name := "y" }))
                                      (ACL2.SExpr.nil))))
                                (ACL2.SExpr.nil))))
                          (ACL2.SExpr.nil))))
                    (ACL2.SExpr.nil)))
                (ACL2.SExpr.cons
                  (ACL2.SExpr.cons
                    (ACL2.SExpr.atom (ACL2.Atom.symbol { package := "ACL2", name := "x" }))
                    (ACL2.SExpr.cons
                      (ACL2.SExpr.cons
                        (ACL2.SExpr.atom (ACL2.Atom.symbol { package := "ACL2", name := "+" }))
                        (ACL2.SExpr.cons
                          (ACL2.SExpr.atom (ACL2.Atom.number (ACL2.Number.rational 1 2)))
                          (ACL2.SExpr.cons
                            (ACL2.SExpr.cons
                              (ACL2.SExpr.atom (ACL2.Atom.symbol { package := "ACL2", name := "*" }))
                              (ACL2.SExpr.cons
                                (ACL2.SExpr.atom (ACL2.Atom.number (ACL2.Number.rational 1 2)))
                                (ACL2.SExpr.cons
                                  (ACL2.SExpr.atom (ACL2.Atom.symbol { package := "ACL2", name := "N" }))
                                  (ACL2.SExpr.nil))))
                            (ACL2.SExpr.nil))))
                      (ACL2.SExpr.nil)))
                  (ACL2.SExpr.cons
                    (ACL2.SExpr.cons
                      (ACL2.SExpr.atom (ACL2.Atom.symbol { package := "ACL2", name := "y" }))
                      (ACL2.SExpr.cons
                        (ACL2.SExpr.cons
                          (ACL2.SExpr.atom (ACL2.Atom.symbol { package := "ACL2", name := "expt" }))
                          (ACL2.SExpr.cons
                            (ACL2.SExpr.atom (ACL2.Atom.number (ACL2.Number.int 2)))
                            (ACL2.SExpr.cons
                              (ACL2.SExpr.cons
                                (ACL2.SExpr.atom (ACL2.Atom.symbol { package := "ACL2", name := "clog2" }))
                                (ACL2.SExpr.cons
                                  (ACL2.SExpr.cons
                                    (ACL2.SExpr.atom (ACL2.Atom.symbol { package := "ACL2", name := "+" }))
                                    (ACL2.SExpr.cons
                                      (ACL2.SExpr.atom (ACL2.Atom.number (ACL2.Number.rational 1 2)))
                                      (ACL2.SExpr.cons
                                        (ACL2.SExpr.cons
                                          (ACL2.SExpr.atom (ACL2.Atom.symbol { package := "ACL2", name := "*" }))
                                          (ACL2.SExpr.cons
                                            (ACL2.SExpr.atom (ACL2.Atom.number (ACL2.Number.rational 1 2)))
                                            (ACL2.SExpr.cons
                                              (ACL2.SExpr.atom (ACL2.Atom.symbol { package := "ACL2", name := "n" }))
                                              (ACL2.SExpr.nil))))
                                        (ACL2.SExpr.nil))))
                                  (ACL2.SExpr.nil)))
                              (ACL2.SExpr.nil))))
                        (ACL2.SExpr.nil)))
                    (ACL2.SExpr.nil)))))
            (ACL2.SExpr.nil))))
      (ACL2.SExpr.cons
        (ACL2.SExpr.cons
          (ACL2.SExpr.atom (ACL2.Atom.string "Subgoal *1/5"))
          (ACL2.SExpr.cons
            (ACL2.SExpr.atom (ACL2.Atom.keyword "use"))
            (ACL2.SExpr.cons
              (ACL2.SExpr.cons
                (ACL2.SExpr.atom (ACL2.Atom.keyword "instance"))
                (ACL2.SExpr.cons
                  (ACL2.SExpr.cons
                    (ACL2.SExpr.atom (ACL2.Atom.keyword "theorem"))
                    (ACL2.SExpr.cons
                      (ACL2.SExpr.cons
                        (ACL2.SExpr.atom (ACL2.Atom.symbol { package := "ACL2", name := "implies" }))
                        (ACL2.SExpr.cons
                          (ACL2.SExpr.cons
                            (ACL2.SExpr.atom (ACL2.Atom.symbol { package := "ACL2", name := "<=" }))
                            (ACL2.SExpr.cons
                              (ACL2.SExpr.atom (ACL2.Atom.symbol { package := "ACL2", name := "x" }))
                              (ACL2.SExpr.cons
                                (ACL2.SExpr.atom (ACL2.Atom.symbol { package := "ACL2", name := "y" }))
                                (ACL2.SExpr.nil))))
                          (ACL2.SExpr.cons
                            (ACL2.SExpr.cons
                              (ACL2.SExpr.atom (ACL2.Atom.symbol { package := "ACL2", name := "<=" }))
                              (ACL2.SExpr.cons
                                (ACL2.SExpr.cons
                                  (ACL2.SExpr.atom (ACL2.Atom.symbol { package := "ACL2", name := "*" }))
                                  (ACL2.SExpr.cons
                                    (ACL2.SExpr.atom (ACL2.Atom.number (ACL2.Number.int 2)))
                                    (ACL2.SExpr.cons
                                      (ACL2.SExpr.atom (ACL2.Atom.symbol { package := "ACL2", name := "x" }))
                                      (ACL2.SExpr.nil))))
                                (ACL2.SExpr.cons
                                  (ACL2.SExpr.cons
                                    (ACL2.SExpr.atom (ACL2.Atom.symbol { package := "ACL2", name := "*" }))
                                    (ACL2.SExpr.cons
                                      (ACL2.SExpr.atom (ACL2.Atom.number (ACL2.Number.int 2)))
                                      (ACL2.SExpr.cons
                                        (ACL2.SExpr.atom (ACL2.Atom.symbol { package := "ACL2", name := "y" }))
                                        (ACL2.SExpr.nil))))
                                  (ACL2.SExpr.nil))))
                            (ACL2.SExpr.nil))))
                      (ACL2.SExpr.nil)))
                  (ACL2.SExpr.cons
                    (ACL2.SExpr.cons
                      (ACL2.SExpr.atom (ACL2.Atom.symbol { package := "ACL2", name := "x" }))
                      (ACL2.SExpr.cons
                        (ACL2.SExpr.cons
                          (ACL2.SExpr.atom (ACL2.Atom.symbol { package := "ACL2", name := "*" }))
                          (ACL2.SExpr.cons
                            (ACL2.SExpr.atom (ACL2.Atom.number (ACL2.Number.rational 1 2)))
                            (ACL2.SExpr.cons
                              (ACL2.SExpr.atom (ACL2.Atom.symbol { package := "ACL2", name := "N" }))
                              (ACL2.SExpr.nil))))
                        (ACL2.SExpr.nil)))
                    (ACL2.SExpr.cons
                      (ACL2.SExpr.cons
                        (ACL2.SExpr.atom (ACL2.Atom.symbol { package := "ACL2", name := "y" }))
                        (ACL2.SExpr.cons
                          (ACL2.SExpr.cons
                            (ACL2.SExpr.atom (ACL2.Atom.symbol { package := "ACL2", name := "expt" }))
                            (ACL2.SExpr.cons
                              (ACL2.SExpr.atom (ACL2.Atom.number (ACL2.Number.int 2)))
                              (ACL2.SExpr.cons
                                (ACL2.SExpr.cons
                                  (ACL2.SExpr.atom (ACL2.Atom.symbol { package := "ACL2", name := "clog2" }))
                                  (ACL2.SExpr.cons
                                    (ACL2.SExpr.cons
                                      (ACL2.SExpr.atom (ACL2.Atom.symbol { package := "ACL2", name := "*" }))
                                      (ACL2.SExpr.cons
                                        (ACL2.SExpr.atom (ACL2.Atom.number (ACL2.Number.rational 1 2)))
                                        (ACL2.SExpr.cons
                                          (ACL2.SExpr.atom (ACL2.Atom.symbol { package := "ACL2", name := "n" }))
                                          (ACL2.SExpr.nil))))
                                    (ACL2.SExpr.nil)))
                                (ACL2.SExpr.nil))))
                          (ACL2.SExpr.nil)))
                      (ACL2.SExpr.nil)))))
              (ACL2.SExpr.nil))))
        (ACL2.SExpr.nil)))
    (ACL2.SExpr.nil)) -/
  sorry

theorem clog2_is_correct (n : SExpr) : Logic.toBool ((Logic.implies (Logic.posp n) (Logic.and (Logic.lt (Logic.expt (SExpr.atom (.number (.int (2)))) (Logic.plus (SExpr.atom (.number (.int (-1)))) (clog2 n))) n) (Logic.le n (Logic.expt (SExpr.atom (.number (.int (2)))) (clog2 n)))))) = true :=
  sorry

partial def nbr_calls_clog2 (n : SExpr) : SExpr :=
  (Logic.if_ (Logic.zp n) (SExpr.atom (.number (.int (1)))) (Logic.if_ (Logic.eq n (SExpr.atom (.number (.int (1))))) (SExpr.atom (.number (.int (1)))) (Logic.if_ (Logic.evenp n) (Logic.plus (SExpr.atom (.number (.int (1)))) (nbr_calls_clog2 (Logic.div n (SExpr.atom (.number (.int (2))))))) (Logic.plus (SExpr.atom (.number (.int (1)))) (nbr_calls_clog2 (Logic.div (Logic.plus (SExpr.atom (.number (.int (1)))) n) (SExpr.atom (.number (.int (2))))))))))

theorem nbr_calls_clog2_eq_1_plus_clog2 (n : SExpr) : Logic.toBool ((Logic.implies (Logic.posp n) (Logic.equal (nbr_calls_clog2 n) (Logic.plus (SExpr.atom (.number (.int (1)))) (clog2 n))))) = true :=
  sorry

partial def nbr_calls_flog2 (n : SExpr) : SExpr :=
  (Logic.if_ (Logic.zp n) (SExpr.atom (.number (.int (1)))) (Logic.if_ (Logic.evenp n) (Logic.plus (SExpr.atom (.number (.int (1)))) (nbr_calls_flog2 (Logic.div n (SExpr.atom (.number (.int (2))))))) (Logic.plus (SExpr.atom (.number (.int (1)))) (nbr_calls_flog2 (Logic.minus n (SExpr.atom (.number (.int (1)))))))))

theorem nbr_calls_flog2_lower_bound (n : SExpr) : Logic.toBool ((Logic.implies (Logic.posp n) (Logic.le (Logic.plus (SExpr.atom (.number (.int (2)))) (flog2 n)) (nbr_calls_flog2 n)))) = true :=
  sorry

theorem nbr_calls_flog2_upper_bound (n : SExpr) : Logic.toBool ((Logic.and (Logic.implies (Logic.and (Logic.posp n) (Logic.evenp n)) (Logic.le (nbr_calls_flog2 n) (Logic.plus (SExpr.atom (.number (.int (1)))) (Logic.times (SExpr.atom (.number (.int (2)))) (flog2 n))))) (Logic.implies (Logic.and (Logic.posp n) (Logic.oddp n)) (Logic.le (nbr_calls_flog2 n) (Logic.plus (SExpr.atom (.number (.int (2)))) (Logic.times (SExpr.atom (.number (.int (2)))) (flog2 n))))))) = true :=
  sorry

theorem nbr_calls_flog2_is_logarithmic (n : SExpr) : Logic.toBool ((Logic.implies (Logic.posp n) (Logic.and (Logic.le (Logic.plus (SExpr.atom (.number (.int (2)))) (flog2 n)) (nbr_calls_flog2 n)) (Logic.le (nbr_calls_flog2 n) (Logic.plus (SExpr.atom (.number (.int (2)))) (Logic.times (SExpr.atom (.number (.int (2)))) (flog2 n))))))) = true := /- hints: ACL2.SExpr.cons
  (ACL2.SExpr.atom (ACL2.Atom.keyword "hints"))
  (ACL2.SExpr.cons
    (ACL2.SExpr.cons
      (ACL2.SExpr.cons
        (ACL2.SExpr.atom (ACL2.Atom.string "Goal"))
        (ACL2.SExpr.cons
          (ACL2.SExpr.atom (ACL2.Atom.keyword "use"))
          (ACL2.SExpr.cons
            (ACL2.SExpr.atom (ACL2.Atom.symbol { package := "ACL2", name := "nbr-calls-flog2-upper-bound" }))
            (ACL2.SExpr.nil))))
      (ACL2.SExpr.nil))
    (ACL2.SExpr.nil)) -/
  sorry

