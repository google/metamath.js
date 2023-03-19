include "ccntz.mm"
include "cfv.mm"
include "eqid.mm"
include "ccmn.mm"
include "wcel.mm"
include "cmnd.mm"
include "cmnmnd.mm"
include "syl.mm"
include "cntzcmnf.mm"
include "gsumzmhm.mm"

theorem gsummhm
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cF: class F
  let cG: class G
  let cH: class H
  let cK: class K
  let cV: class V
  let c.0: class .0.
  assume gsummhm.b: |- B = ( Base ` G )
  assume gsummhm.z: |- .0. = ( 0g ` G )
  assume gsummhm.g: |- ( ph -> G e. CMnd )
  assume gsummhm.h: |- ( ph -> H e. Mnd )
  assume gsummhm.a: |- ( ph -> A e. V )
  assume gsummhm.k: |- ( ph -> K e. ( G MndHom H ) )
  assume gsummhm.f: |- ( ph -> F : A --> B )
  assume gsummhm.w: |- ( ph -> F finSupp .0. )


  assert |- ( ph -> ( H gsum ( K o. F ) ) = ( K ` ( G gsum F ) ) )

  proof
    wph
    cA
    cB
    cF
    cG
    cH
    cK
    cV
    c.0
    cG
    ccntz
    cfv
    #
    gsummhm.b
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
    gsummhm.g
    cG
    cmnmnd
    syl
    gsummhm.h
    gsummhm.a
    gsummhm.k
    gsummhm.f
    wph
    cA
    cB
    cF
    cG
    @0
    gsummhm.b
    @1
    gsummhm.g
    gsummhm.f
    cntzcmnf
    gsummhm.z
    gsummhm.w
    gsumzmhm
end
