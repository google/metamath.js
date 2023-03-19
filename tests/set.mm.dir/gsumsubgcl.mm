include "cabl.mm"
include "wcel.mm"
include "ccmn.mm"
include "ablcmn.mm"
include "syl.mm"
include "csubg.mm"
include "cfv.mm"
include "csubmnd.mm"
include "subgsubm.mm"
include "gsumsubmcl.mm"

theorem gsumsubgcl
  let wph: wff ph
  let cA: class A
  let cS: class S
  let cF: class F
  let cG: class G
  let cV: class V
  let c.0: class .0.
  assume gsumsubgcl.z: |- .0. = ( 0g ` G )
  assume gsumsubgcl.g: |- ( ph -> G e. Abel )
  assume gsumsubgcl.a: |- ( ph -> A e. V )
  assume gsumsubgcl.s: |- ( ph -> S e. ( SubGrp ` G ) )
  assume gsumsubgcl.f: |- ( ph -> F : A --> S )
  assume gsumsubgcl.w: |- ( ph -> F finSupp .0. )


  assert |- ( ph -> ( G gsum F ) e. S )

  proof
    wph
    cA
    cS
    cF
    cG
    cV
    c.0
    gsumsubgcl.z
    wph
    cG
    cabl
    wcel
    cG
    ccmn
    wcel
    gsumsubgcl.g
    cG
    ablcmn
    syl
    gsumsubgcl.a
    wph
    cS
    cG
    csubg
    cfv
    wcel
    cS
    cG
    csubmnd
    cfv
    wcel
    gsumsubgcl.s
    cS
    cG
    subgsubm
    syl
    gsumsubgcl.f
    gsumsubgcl.w
    gsumsubmcl
end
