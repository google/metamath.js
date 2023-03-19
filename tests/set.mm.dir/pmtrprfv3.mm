include "wcel.mm"
include "w3a.mm"
include "wne.mm"
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
include "simp1.mm"
include "3ad2ant2.mm"
include "simp22.mm"
include "prssi.mm"
include "syl2anc.mm"
include "wi.mm"
include "pr2nelem.mm"
include "3expia.mm"
include "3adant3.mm"
include "com12.mm"
include "3ad2ant1.mm"
include "impcom.mm"
include "3adant1.mm"
include "simp23.mm"
include "pmtrfv.mm"
include "syl31anc.mm"
include "necom.mm"
include "biimpi.mm"
include "3ad2ant3.mm"
include "nelprd.mm"
include "iffalsed.mm"
include "eqtrd.mm"

theorem pmtrprfv3
  let cD: class D
  let cT: class T
  let cV: class V
  let cX: class X
  let cY: class Y
  let cZ: class Z
  let vd: setvar d
  let vp: setvar p
  let vy: setvar y
  let vz: setvar z
  let cP: class P
  assume pmtrfval.t: |- T = ( pmTrsp ` D )


  assert |- ( ( D e. V /\ ( X e. D /\ Y e. D /\ Z e. D ) /\ ( X =/= Y /\ X =/= Z /\ Y =/= Z ) ) -> ( ( T ` { X , Y } ) ` Z ) = Z )

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
    cZ
    cD
    wcel
    #
    w3a
    #
    cX
    cY
    wne
    #
    cX
    cZ
    wne
    #
    cY
    cZ
    wne
    #
    w3a
    #
    w3a
    #
    cZ
    cX
    cY
    cpr
    #
    cT
    cfv
    cfv
    #
    cZ
    @10
    wcel
    #
    @10
    cZ
    csn
    cdif
    cuni
    #
    cZ
    cif
    #
    cZ
    @9
    @0
    @10
    cD
    wss
    #
    @10
    c2o
    cen
    wbr
    #
    @3
    @11
    @14
    wceq
    @0
    @4
    @8
    simp1
    @9
    @1
    @2
    @15
    @4
    @0
    @1
    @8
    @1
    @2
    @3
    simp1
    3ad2ant2
    @0
    @1
    @2
    @3
    @8
    simp22
    cX
    cY
    cD
    prssi
    syl2anc
    @4
    @8
    @16
    @0
    @8
    @4
    @16
    @5
    @6
    @4
    @16
    wi
    @7
    @4
    @5
    @16
    @1
    @2
    @5
    @16
    wi
    @3
    @1
    @2
    @5
    @16
    cX
    cY
    cD
    cD
    pr2nelem
    3expia
    3adant3
    com12
    3ad2ant1
    impcom
    3adant1
    @0
    @1
    @2
    @3
    @8
    simp23
    cD
    @10
    cT
    cV
    cZ
    pmtrfval.t
    pmtrfv
    syl31anc
    @9
    @12
    @13
    cZ
    @9
    cZ
    cX
    cY
    @8
    @0
    cZ
    cX
    wne
    #
    @4
    @6
    @5
    @17
    @7
    @6
    @17
    cX
    cZ
    necom
    biimpi
    3ad2ant2
    3ad2ant3
    @8
    @0
    cZ
    cY
    wne
    #
    @4
    @7
    @5
    @18
    @6
    @7
    @18
    cY
    cZ
    necom
    biimpi
    3ad2ant3
    3ad2ant3
    nelprd
    iffalsed
    eqtrd
end
