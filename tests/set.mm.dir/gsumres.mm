include "ccntz.mm"
include "cfv.mm"
include "eqid.mm"
include "ccmn.mm"
include "wcel.mm"
include "cmnd.mm"
include "cmnmnd.mm"
include "syl.mm"
include "cntzcmnf.mm"
include "gsumzres.mm"

theorem gsumres
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cF: class F
  let cG: class G
  let cV: class V
  let cW: class W
  let c.0: class .0.
  assume gsumcl.b: |- B = ( Base ` G )
  assume gsumcl.z: |- .0. = ( 0g ` G )
  assume gsumcl.g: |- ( ph -> G e. CMnd )
  assume gsumcl.a: |- ( ph -> A e. V )
  assume gsumcl.f: |- ( ph -> F : A --> B )
  assume gsumres.s: |- ( ph -> ( F supp .0. ) C_ W )
  assume gsumres.w: |- ( ph -> F finSupp .0. )


  assert |- ( ph -> ( G gsum ( F |` W ) ) = ( G gsum F ) )

  proof
    wph
    cA
    cB
    cF
    cG
    cV
    cW
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
    gsumres.s
    gsumres.w
    gsumzres
end
