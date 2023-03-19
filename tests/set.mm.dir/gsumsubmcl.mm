include "ccntz.mm"
include "cfv.mm"
include "eqid.mm"
include "ccmn.mm"
include "wcel.mm"
include "cmnd.mm"
include "cmnmnd.mm"
include "syl.mm"
include "cbs.mm"
include "csubmnd.mm"
include "wss.mm"
include "submss.mm"
include "fssd.mm"
include "cntzcmnf.mm"
include "gsumzsubmcl.mm"

theorem gsumsubmcl
  let wph: wff ph
  let cA: class A
  let cS: class S
  let cF: class F
  let cG: class G
  let cV: class V
  let c.0: class .0.
  assume gsumsubmcl.z: |- .0. = ( 0g ` G )
  assume gsumsubmcl.g: |- ( ph -> G e. CMnd )
  assume gsumsubmcl.a: |- ( ph -> A e. V )
  assume gsumsubmcl.s: |- ( ph -> S e. ( SubMnd ` G ) )
  assume gsumsubmcl.f: |- ( ph -> F : A --> S )
  assume gsumsubmcl.w: |- ( ph -> F finSupp .0. )


  assert |- ( ph -> ( G gsum F ) e. S )

  proof
    wph
    cA
    cS
    cF
    cG
    cV
    c.0
    cG
    ccntz
    cfv
    #
    gsumsubmcl.z
    @0
    eqid
    #
    wph
    cG
    ccmn
    wcel
    cG
    cmnd
    wcel
    gsumsubmcl.g
    cG
    cmnmnd
    syl
    gsumsubmcl.a
    gsumsubmcl.s
    gsumsubmcl.f
    wph
    cA
    cG
    cbs
    cfv
    #
    cF
    cG
    @0
    @2
    eqid
    #
    @1
    gsumsubmcl.g
    wph
    cA
    cS
    @2
    cF
    gsumsubmcl.f
    wph
    cS
    cG
    csubmnd
    cfv
    wcel
    cS
    @2
    wss
    gsumsubmcl.s
    @2
    cS
    cG
    @3
    submss
    syl
    fssd
    cntzcmnf
    gsumsubmcl.w
    gsumzsubmcl
end
