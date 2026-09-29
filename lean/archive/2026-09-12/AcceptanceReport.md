# 2026-09-12 修订验证结果

完整恢复后的工程已通过 Lean 4.19.0 全项目构建；新增模块、全部 419 个清单声明及扩展审计的编译命令均成功。静态源码检查与清单检查通过。详细记录见 validation/2026-09-12。

## 修正

- lem:spine / U38：增加同一无限路径概率空间上的 Markov 链、全部有限维分布和指定边际；结合原有增量和尾界结果对应原文。
- lem:momentODE / U48：增加任意正时间紧区间上的可积导数及积分增量恒等式，以已有 HasIntegralDerivativeOn 定义明确表达局部绝对连续性。

论文和外部输入文件保持原始校验值。两个修正模块与误删前最终版本的校验值一致。

## 信任范围

无限链新增结果只依赖 Lean 标准公理；局部绝对连续性新增结果依赖标准公理与 H1a/H1b。主 profile 定理依赖 H1a/H1b/H2，sharpness 定理依赖 H3。全部审计输出未出现四项既定外部输入以外的非标准公理。

这表示在接受约定外部输入的条件下，修订后的形式化推导通过检查；外部文献结论本身未在此项目重新证明。清单覆盖检查不单独构成自然语言与形式化陈述等价的证明。

PowerShell 审计脚本的既有直接导入白名单已补齐三个原始模块；当前平台实际运行的是对应 Python 静态检查与 Bash 清单检查，没有运行 PowerShell。

## 工具版本与冻结文件

- Lean 4.19.0，commit `6caaee842e94`，arm64-apple-darwin23.6.0。
- Lake 5.0.0-6caaee8。
- mathlib v4.19.0，commit `c44e0c8ee63ca166450922a373c7409c5d26b00b`；依赖版本由 lake-manifest.json 固定。
- DR_Yaglom.tex SHA-256：`652c080e30cfc8cb37ea9636ae74e4c0b30875e1a69db5ae81008137b5a0b82a`。
- HumanInputs.lean SHA-256：`2f35158a78164c7ffe0e8def2049a5c6c9a747fa3671b38965110677752f465e`。

## 原始 prompt 的交付清单

1. DerridaRetaux/、DerridaRetaux.lean、lakefile.toml、lake-manifest.json、lean-toolchain：完整源工程与锁定依赖。
2. AcceptanceReport.md：本报告。
3. STATEMENT_LEDGER.csv：15 个编号结果；compiled_declaration_custom_axioms 列逐声明记录实际非标准公理名称。
4. EQUATION_LEDGER.csv：82 条公式，同样含逐声明依赖。
5. UNNUMBERED_LEDGER.csv：U01–U62，同样含逐声明依赖。
6. EXTERNAL_INTERFACES.md：沿用唯一规范文件，含四项冻结签名、出处和假设对应。
7. DEPENDENCY_DAG.md：包含两个补充模块、公开声明及已完成状态。
8. ReuseAudit.md：保留原交付中的复用调查；本轮没有引入其他工程作为依赖。
9. ProofObligations.md：当前没有遗留项。
10. BLOCKERS.md：内容为 none。
11. build-final.log、sorry-final.log、axioms-final.log：本次实际构建、静态扫描及公理输出，旧日志归档于 validation/2026-09-11。
12. HANDOFF.md：简明交接说明。

## 编译得到的公开定理类型

完整 419 个声明的类型及公理输出保存在 `validation/2026-09-12/all-source-axioms.log`，并汇总于 `axioms-final.log`。其中包含主定理、sharpness、core 层和两个补充声明；不是仅打印主要结论。四个外部声明的精确签名见 EXTERNAL_INTERFACES.md 与冻结 HumanInputs.lean。

本轮采用已有逐点导数及连续性推出紧区间积分增量表示，补齐局部绝对连续性；未按原 prompt 建议的先 AC 后 C¹ 顺序重写现有证明。公开结论及外部输入没有因此改变。

### DerridaRetaux.FixedArity.profile

```text
DerridaRetaux.FixedArity.profile (m : Nat) (data : DerridaRetaux.ProfileInitialData m) :
  And
    (∀ (R : Real),
      LE.le.{0} 0 R →
        ∃ error,
          And (Filter.Tendsto.{0, 0} error Filter.atTop.{0} (nhds.{0} 0))
            (∀ (n : Nat),
              LT.lt.{0} 0 n →
                ∀ (x : Real),
                  LE.le.{0} 0 x →
                    LE.le.{0} x R →
                      LE.le.{0}
                        (abs.{0}
                          (HSub.hSub.{0, 0, 0}
                            (HMul.hMul.{0, 0, 0} (HPow.hPow.{0, 0, 0} (↑n) 2)
                              (DerridaRetaux.rho m
                                (DerridaRetaux.orbit m
                                  (DerridaRetaux.CriticalInitialData.law
                                    (DerridaRetaux.ProfileInitialData.toCriticalInitialData data))
                                  n)
                                (DerridaRetaux.gridIndex n x)))
                            (HMul.hMul.{0, 0, 0} 4 (Real.exp (HMul.hMul.{0, 0, 0} (-2) x)))))
                        (error n)))
    (And
      (Filter.Tendsto.{0, 0}
        (fun n =>
          HMul.hMul.{0, 0, 0} (↑n)
            (DerridaRetaux.excess m
              (DerridaRetaux.orbit m
                (DerridaRetaux.CriticalInitialData.law (DerridaRetaux.ProfileInitialData.toCriticalInitialData data))
                n)))
        Filter.atTop.{0} (nhds.{0} (HDiv.hDiv.{0, 0, 0} 2 (HSub.hSub.{0, 0, 0} (↑m) 1))))
      (And
        (Filter.Tendsto.{0, 0}
          (fun n =>
            HMul.hMul.{0, 0, 0} (HPow.hPow.{0, 0, 0} (↑n) 2)
              (DerridaRetaux.survival
                (DerridaRetaux.orbit m
                  (DerridaRetaux.CriticalInitialData.law (DerridaRetaux.ProfileInitialData.toCriticalInitialData data))
                  n)))
          Filter.atTop.{0} (nhds.{0} (HDiv.hDiv.{0, 0, 0} 4 (HPow.hPow.{0, 0, 0} (HSub.hSub.{0, 0, 0} (↑m) 1) 2))))
        (And
          (Filter.Tendsto.{0, 0}
            (fun n =>
              HMul.hMul.{0, 0, 0} (HPow.hPow.{0, 0, 0} (↑n) 2)
                (HSub.hSub.{0, 0, 0}
                  (DerridaRetaux.excess m
                    (DerridaRetaux.orbit m
                      (DerridaRetaux.CriticalInitialData.law
                        (DerridaRetaux.ProfileInitialData.toCriticalInitialData data))
                      n))
                  (DerridaRetaux.excess m
                    (DerridaRetaux.orbit m
                      (DerridaRetaux.CriticalInitialData.law
                        (DerridaRetaux.ProfileInitialData.toCriticalInitialData data))
                      (HAdd.hAdd.{0, 0, 0} n 1)))))
            Filter.atTop.{0} (nhds.{0} (HDiv.hDiv.{0, 0, 0} 2 (HSub.hSub.{0, 0, 0} (↑m) 1))))
          (And
            (Filter.Tendsto.{0, 0}
              (fun n =>
                HMul.hMul.{0, 0, 0} (HPow.hPow.{0, 0, 0} (↑n) 2)
                  (DerridaRetaux.probabilityFirstMoment
                    (DerridaRetaux.orbit m
                      (DerridaRetaux.CriticalInitialData.law
                        (DerridaRetaux.ProfileInitialData.toCriticalInitialData data))
                      n)))
              Filter.atTop.{0}
              (nhds.{0}
                (HDiv.hDiv.{0, 0, 0} (HMul.hMul.{0, 0, 0} 4 ↑m) (HPow.hPow.{0, 0, 0} (HSub.hSub.{0, 0, 0} (↑m) 1) 3))))
            (And
              (∀ (k : Nat),
                LE.le.{0} 1 k →
                  Filter.Tendsto.{0, 0}
                    (fun n =>
                      HMul.hMul.{0, 0, 0} (HPow.hPow.{0, 0, 0} (↑n) 2)
                        (DerridaRetaux.ProbabilityMass.mass
                          (DerridaRetaux.orbit m
                            (DerridaRetaux.CriticalInitialData.law
                              (DerridaRetaux.ProfileInitialData.toCriticalInitialData data))
                            n)
                          k))
                    Filter.atTop.{0}
                    (nhds.{0}
                      (HDiv.hDiv.{0, 0, 0} 4
                        (HMul.hMul.{0, 0, 0} (HSub.hSub.{0, 0, 0} (↑m) 1) (HPow.hPow.{0, 0, 0} (↑m) k)))))
              (And
                (Filter.Tendsto.{0, 0}
                  (fun n =>
                    HDiv.hDiv.{0, 0, 0}
                      (DerridaRetaux.probabilityFirstMoment
                        (DerridaRetaux.orbit m
                          (DerridaRetaux.CriticalInitialData.law
                            (DerridaRetaux.ProfileInitialData.toCriticalInitialData data))
                          n))
                      (DerridaRetaux.survival
                        (DerridaRetaux.orbit m
                          (DerridaRetaux.CriticalInitialData.law
                            (DerridaRetaux.ProfileInitialData.toCriticalInitialData data))
                          n)))
                  Filter.atTop.{0} (nhds.{0} (HDiv.hDiv.{0, 0, 0} (↑m) (HSub.hSub.{0, 0, 0} (↑m) 1))))
                (Asymptotics.IsBigO.{0, 0, 0} Filter.atTop.{0}
                  (fun n =>
                    DerridaRetaux.conditionalPositiveL1Error m
                      (DerridaRetaux.orbit m
                        (DerridaRetaux.CriticalInitialData.law
                          (DerridaRetaux.ProfileInitialData.toCriticalInitialData data))
                        n))
                  fun n => HDiv.hDiv.{0, 0, 0} (Real.log ↑(HAdd.hAdd.{0, 0, 0} n 2)) ↑(HAdd.hAdd.{0, 0, 0} n 1))))))))
```

### DerridaRetaux.FixedArity.sharpness

```text
DerridaRetaux.FixedArity.sharpness (m : Nat) (r : Real) (hm : LE.le.{0} 2 m) (hr₀ : LE.le.{0} 0 r)
  (hr₃ : LT.lt.{0} r 3) :
  ∃ p₀,
    And (DerridaRetaux.Critical m p₀)
      (And (Not (DerridaRetaux.IsDirac p₀))
        (And (DerridaRetaux.RealTiltSummable m r p₀)
          (And (Not (DerridaRetaux.TiltSummable m 3 p₀))
            (Not
              (Filter.Tendsto.{0, 0}
                (fun n =>
                  HMul.hMul.{0, 0, 0} (↑n)
                    (HSub.hSub.{0, 0, 0} (DerridaRetaux.tiltedPartition m (DerridaRetaux.orbit m p₀ n)) 1))
                Filter.atTop.{0} (nhds.{0} (HDiv.hDiv.{0, 0, 0} 2 (HSub.hSub.{0, 0, 0} (↑m) 1))))))))
```

### DerridaRetaux.FixedArity.cubicWeightedInfiniteChain

```text
DerridaRetaux.FixedArity.cubicWeightedInfiniteChain (m : Nat) (data : DerridaRetaux.ProfileInitialData m) :
  ∃ μ,
    And (MeasureTheory.IsProbabilityMeasure.{0} μ)
      (And
        (∀ (n : Nat),
          Eq.{1} (MeasureTheory.Measure.map.{0, 0} (fun w i => w ↑i) μ)
            (PMF.toMeasure.{0} (DerridaRetaux.spinePathPMF m data n)))
        (And
          (∀ (n : Nat),
            Eq.{1} (MeasureTheory.Measure.map.{0, 0} (fun w => w n) μ)
              (PMF.toMeasure.{0} (DerridaRetaux.spineMarginalPMF m data n)))
          (∀ (n : Nat),
            Eq.{1}
              (MeasureTheory.Measure.map.{0, 0} (fun w => Prod.mk.{0, 0} (fun i => w ↑i) (w (HAdd.hAdd.{0, 0, 0} n 1)))
                μ)
              (PMF.toMeasure.{0}
                (PMF.bind.{0, 0} (DerridaRetaux.spinePathPMF m data n) fun u =>
                  PMF.map.{0, 0} (fun k => Prod.mk.{0, 0} u k)
                    (DerridaRetaux.spineKernel m data n (DerridaRetaux.finPathTerminal u)))))))
```

### DerridaRetaux.FixedArity.momentLaplaceLocalIntegralDerivatives

```text
DerridaRetaux.FixedArity.momentLaplaceLocalIntegralDerivatives (m : Nat) (data : DerridaRetaux.ProfileInitialData m)
  (phi : Nat → Nat) (g : (k : Nat) → BoundedContinuousFunction.{0, 0} (↑(DerridaRetaux.gridExhaustionRectangle k)) Real)
  (hphi : Filter.Tendsto.{0, 0} phi Filter.atTop.{0} Filter.atTop.{0})
  (hlim :
    ∀ (k : Nat),
      TendstoUniformly.{0, 0, 0}
        (fun n q =>
          DerridaRetaux.gridBilinearInterp (phi n)
            (DerridaRetaux.orbitScaledGrid m
              (DerridaRetaux.CriticalInitialData.law (DerridaRetaux.ProfileInitialData.toCriticalInitialData data))
              (phi n))
            (↑q).1 (↑q).2)
        (fun q => (g k) q) Filter.atTop.{0}) :
  let A := fun r t => DerridaRetaux.continuumMoment (fun x => DerridaRetaux.gluedExhaustionLimit g t x) r;
  let U := fun t p => DerridaRetaux.continuumLaplace (fun x => DerridaRetaux.gluedExhaustionLimit g t x) p;
  let beta := fun t => DerridaRetaux.gluedExhaustionLimit g t 0;
  ∀ (a b : Real),
    LT.lt.{0} 0 a →
      LE.le.{0} a b →
        And
          (DerridaRetaux.HasIntegralDerivativeOn (A 0)
            (fun t =>
              HAdd.hAdd.{0, 0, 0} (Neg.neg.{0} (beta t)) (HMul.hMul.{0, 0, 0} (1 / 2) (HPow.hPow.{0, 0, 0} (A 0 t) 2)))
            (Set.Icc.{0} a b))
          (And
            (DerridaRetaux.HasIntegralDerivativeOn (A 2)
              (fun t => HSub.hSub.{0, 0, 0} (HMul.hMul.{0, 0, 0} (A 0 t) (A 2 t)) 1) (Set.Icc.{0} a b))
            (And
              (DerridaRetaux.HasIntegralDerivativeOn (A 3) (fun t => HMul.hMul.{0, 0, 0} (A 0 t) (A 3 t))
                (Set.Icc.{0} a b))
              (∀ (p : Real),
                LE.le.{0} 0 p →
                  DerridaRetaux.HasIntegralDerivativeOn (fun t => U t p)
                    (fun t =>
                      HSub.hSub.{0, 0, 0}
                        (HAdd.hAdd.{0, 0, 0} (HMul.hMul.{0, 0, 0} p (U t p))
                          (HMul.hMul.{0, 0, 0} (1 / 2) (HPow.hPow.{0, 0, 0} (U t p) 2)))
                        (beta t))
                    (Set.Icc.{0} a b))))
```
