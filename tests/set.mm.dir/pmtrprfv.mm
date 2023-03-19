include "wcel.mm"
include "wne.mm"
include "w3a.mm"
include "wa.mm"
include "cpr.mm"
include "cfv.mm"
include "csn.mm"
include "cdif.mm"
include "cuni.mm"
include "cif.mm"
include "wss.mm"
include "c2o.mm"
include "cen.mm"
include "wbr.mm"
include "wceq.mm"
include "simpl.mm"
include "simpr1.mm"
include "simpr2.mm"
include "prssi.mm"
include "syl2anc.mm"
include "pr2nelem.mm"
include "adantl.mm"
include "pmtrfv.mm"
include "syl31anc.mm"
include "prid1g.mm"
include "syl.mm"
include "iftrued.mm"
include "difprsnss.mm"
include "a1i.mm"
include "prid2g.mm"
include "simpr3.mm"
include "necomd.mm"
include "eldifsn.mm"
include "sylanbrc.mm"
include "snssd.mm"
include "eqssd.mm"
include "unieqd.mm"
include "unisng.mm"
include "eqtrd.mm"

theorem pmtrprfv
  let cD: class D
  let cT: class T
  let cV: class V
  let cX: class X
  let cY: class Y
  let vd: setvar d
  let vp: setvar p
  let vy: setvar y
  let vz: setvar z
  let cP: class P
  let cZ: class Z
  assume pmtrfval.t: |- T = ( pmTrsp ` D )


  assert |- ( ( D e. V /\ ( X e. D /\ Y e. D /\ X =/= Y ) ) -> ( ( T ` { X , Y } ) ` X ) = Y )

  proof
    cD
    cV
    wcel
    #
    cX
    cD
    wcel
    #
    cY
    cD
    wcel
    #
    cX
    cY
    wne
    #
    w3a
    #
    wa
    #
    cX
    cX
    cY
    cpr
    #
    cT
    cfv
    cfv
    #
    cX
    @6
    wcel
    #
    @6
    cX
    csn
    cdif
    #
    cuni
    #
    cX
    cif
    #
    cY
    @5
    @0
    @6
    cD
    wss
    #
    @6
    c2o
    cen
    wbr
    #
    @1
    @7
    @11
    wceq
    @0
    @4
    simpl
    @5
    @1
    @2
    @12
    @0
    @1
    @2
    @3
    simpr1
    #
    @0
    @1
    @2
    @3
    simpr2
    #
    cX
    cY
    cD
    prssi
    syl2anc
    @4
    @13
    @0
    cX
    cY
    cD
    cD
    pr2nelem
    adantl
    @14
    cD
    @6
    cT
    cV
    cX
    pmtrfval.t
    pmtrfv
    syl31anc
    @5
    @11
    @10
    cY
    @5
    @8
    @10
    cX
    @5
    @1
    @8
    @14
    cX
    cY
    cD
    prid1g
    syl
    iftrued
    @5
    @10
    cY
    csn
    #
    cuni
    #
    cY
    @5
    @9
    @16
    @5
    @9
    @16
    @9
    @16
    wss
    @5
    cX
    cY
    difprsnss
    a1i
    @5
    cY
    @9
    @5
    cY
    @6
    wcel
    #
    cY
    cX
    wne
    cY
    @9
    wcel
    @5
    @2
    @18
    @15
    cX
    cY
    cD
    prid2g
    syl
    @5
    cX
    cY
    @0
    @1
    @2
    @3
    simpr3
    necomd
    cY
    @6
    cX
    eldifsn
    sylanbrc
    snssd
    eqssd
    unieqd
    @5
    @2
    @17
    cY
    wceq
    @15
    cY
    cD
    unisng
    syl
    eqtrd
    eqtrd
    eqtrd
end
