include "cabl.mm"
include "wcel.mm"
include "ccmn.mm"
include "ablcmn.mm"
include "syl.mm"
include "cmnd.mm"
include "cmnmnd.mm"
include "cghm.mm"
include "co.mm"
include "cmhm.mm"
include "invghm.mm"
include "sylib.mm"
include "ghmmhm.mm"
include "gsummhm.mm"

theorem gsuminv
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cF: class F
  let cG: class G
  let cI: class I
  let cV: class V
  let c.0: class .0.
  assume gsuminv.b: |- B = ( Base ` G )
  assume gsuminv.z: |- .0. = ( 0g ` G )
  assume gsuminv.p: |- I = ( invg ` G )
  assume gsuminv.g: |- ( ph -> G e. Abel )
  assume gsuminv.a: |- ( ph -> A e. V )
  assume gsuminv.f: |- ( ph -> F : A --> B )
  assume gsuminv.n: |- ( ph -> F finSupp .0. )


  assert |- ( ph -> ( G gsum ( I o. F ) ) = ( I ` ( G gsum F ) ) )

  proof
    wph
    cA
    cB
    cF
    cG
    cG
    cI
    cV
    c.0
    gsuminv.b
    gsuminv.z
    wph
    cG
    cabl
    wcel
    #
    cG
    ccmn
    wcel
    #
    gsuminv.g
    cG
    ablcmn
    syl
    #
    wph
    @1
    cG
    cmnd
    wcel
    @2
    cG
    cmnmnd
    syl
    gsuminv.a
    wph
    cI
    cG
    cG
    cghm
    co
    wcel
    #
    cI
    cG
    cG
    cmhm
    co
    wcel
    wph
    @0
    @3
    gsuminv.g
    cB
    cG
    cI
    gsuminv.b
    gsuminv.p
    invghm
    sylib
    cG
    cG
    cI
    ghmmhm
    syl
    gsuminv.f
    gsuminv.n
    gsummhm
end
