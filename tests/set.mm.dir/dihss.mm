include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "cfv.mm"
include "clss.mm"
include "wss.mm"
include "eqid.mm"
include "dihlss.mm"
include "lssss.mm"
include "syl.mm"

theorem dihss
  let cB: class B
  let cU: class U
  let cH: class H
  let cI: class I
  let cK: class K
  let cV: class V
  let cW: class W
  let cX: class X
  assume dihss.b: |- B = ( Base ` K )
  assume dihss.h: |- H = ( LHyp ` K )
  assume dihss.i: |- I = ( ( DIsoH ` K ) ` W )
  assume dihss.u: |- U = ( ( DVecH ` K ) ` W )
  assume dihss.v: |- V = ( Base ` U )


  assert |- ( ( ( K e. HL /\ W e. H ) /\ X e. B ) -> ( I ` X ) C_ V )

  proof
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    cX
    cB
    wcel
    wa
    cX
    cI
    cfv
    #
    cU
    clss
    cfv
    #
    wcel
    @0
    cV
    wss
    cB
    @1
    cU
    cH
    cI
    cK
    cW
    cX
    dihss.b
    dihss.h
    dihss.i
    dihss.u
    @1
    eqid
    #
    dihlss
    @1
    @0
    cV
    cU
    dihss.v
    @2
    lssss
    syl
end
