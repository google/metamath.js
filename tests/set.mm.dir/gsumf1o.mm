include "ccntz.mm"
include "cfv.mm"
include "eqid.mm"
include "ccmn.mm"
include "wcel.mm"
include "cmnd.mm"
include "cmnmnd.mm"
include "syl.mm"
include "cntzcmnf.mm"
include "gsumzf1o.mm"

theorem gsumf1o
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F
  let cG: class G
  let cH: class H
  let cV: class V
  let c.0: class .0.
  assume gsumcl.b: |- B = ( Base ` G )
  assume gsumcl.z: |- .0. = ( 0g ` G )
  assume gsumcl.g: |- ( ph -> G e. CMnd )
  assume gsumcl.a: |- ( ph -> A e. V )
  assume gsumcl.f: |- ( ph -> F : A --> B )
  assume gsumcl.w: |- ( ph -> F finSupp .0. )
  assume gsumf1o.h: |- ( ph -> H : C -1-1-onto-> A )


  assert |- ( ph -> ( G gsum F ) = ( G gsum ( F o. H ) ) )

  proof
    wph
    cA
    cB
    cC
    cF
    cG
    cH
    cV
    c.0
    cG
    ccntz
    cfv
    #
    gsumcl.b
    gsumcl.z
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
    gsumcl.g
    cG
    cmnmnd
    syl
    gsumcl.a
    gsumcl.f
    wph
    cA
    cB
    cF
    cG
    @0
    gsumcl.b
    @1
    gsumcl.g
    gsumcl.f
    cntzcmnf
    gsumcl.w
    gsumf1o.h
    gsumzf1o
end
