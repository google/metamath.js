include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "cfv.mm"
include "wceq.mm"
include "cv.mm"
include "wn.mm"
include "cmee.mm"
include "co.mm"
include "cjn.mm"
include "cdic.mm"
include "cdvh.mm"
include "clsm.mm"
include "wi.mm"
include "catm.mm"
include "wral.mm"
include "clss.mm"
include "crio.mm"
include "cif.mm"
include "eqid.mm"
include "dihval.mm"
include "iftrue.mm"
include "sylan9eq.mm"
include "anasss.mm"

theorem dihvalb
  let cB: class B
  let cD: class D
  let cH: class H
  let cI: class I
  let cK: class K
  let c.le: class .<_
  let cV: class V
  let cW: class W
  let cX: class X
  let vq: setvar q
  let vu: setvar u
  assume dihvalb.b: |- B = ( Base ` K )
  assume dihvalb.l: |- .<_ = ( le ` K )
  assume dihvalb.h: |- H = ( LHyp ` K )
  assume dihvalb.i: |- I = ( ( DIsoH ` K ) ` W )
  assume dihvalb.d: |- D = ( ( DIsoB ` K ) ` W )


  assert |- ( ( ( K e. V /\ W e. H ) /\ ( X e. B /\ X .<_ W ) ) -> ( I ` X ) = ( D ` X ) )

  proof
    cK
    cV
    wcel
    cW
    cH
    wcel
    wa
    #
    cX
    cB
    wcel
    #
    cX
    cW
    c.le
    wbr
    #
    cX
    cI
    cfv
    #
    cX
    cD
    cfv
    #
    wceq
    @0
    @1
    wa
    @2
    @3
    @2
    @4
    vq
    cv
    #
    cW
    c.le
    wbr
    wn
    @5
    cX
    cW
    cK
    cmee
    cfv
    #
    co
    #
    cK
    cjn
    cfv
    #
    co
    cX
    wceq
    wa
    vu
    cv
    @5
    cW
    cK
    cdic
    cfv
    cfv
    #
    cfv
    @7
    cD
    cfv
    cW
    cK
    cdvh
    cfv
    cfv
    #
    clsm
    cfv
    #
    co
    wceq
    wi
    vq
    cK
    catm
    cfv
    #
    wral
    vu
    @10
    clss
    cfv
    #
    crio
    #
    cif
    @4
    vu
    @12
    cB
    @9
    cD
    @11
    @13
    @10
    cH
    cI
    @8
    cK
    c.le
    @6
    cV
    cW
    cX
    vq
    dihvalb.b
    dihvalb.l
    @8
    eqid
    @6
    eqid
    @12
    eqid
    dihvalb.h
    dihvalb.i
    dihvalb.d
    @9
    eqid
    @10
    eqid
    @13
    eqid
    @11
    eqid
    dihval
    @2
    @4
    @14
    iftrue
    sylan9eq
    anasss
end
