include "clat.mm"
include "wcel.mm"
include "w3a.mm"
include "cop.mm"
include "cdm.mm"
include "wa.mm"
include "co.mm"
include "wceq.mm"
include "cxp.mm"
include "opelxpi.mm"
include "3adant1.mm"
include "cpo.mm"
include "cjn.mm"
include "cfv.mm"
include "eqid.mm"
include "islat.mm"
include "simprr.mm"
include "sylbi.mm"
include "3ad2ant1.mm"
include "eleqtrrd.mm"
include "ancoms.mm"
include "jca.mm"
include "latpos.mm"
include "meetcom.mm"
include "syl3anl1.mm"
include "mpdan.mm"

theorem latmcom
  let cB: class B
  let cK: class K
  let c.an: class ./\
  let cX: class X
  let cY: class Y
  assume latmcom.b: |- B = ( Base ` K )
  assume latmcom.m: |- ./\ = ( meet ` K )


  assert |- ( ( K e. Lat /\ X e. B /\ Y e. B ) -> ( X ./\ Y ) = ( Y ./\ X ) )

  proof
    cK
    clat
    wcel
    #
    cX
    cB
    wcel
    #
    cY
    cB
    wcel
    #
    w3a
    #
    cX
    cY
    cop
    #
    c.an
    cdm
    #
    wcel
    #
    cY
    cX
    cop
    #
    @5
    wcel
    #
    wa
    #
    cX
    cY
    c.an
    co
    cY
    cX
    c.an
    co
    wceq
    #
    @3
    @6
    @8
    @3
    @4
    cB
    cB
    cxp
    #
    @5
    @1
    @2
    @4
    @11
    wcel
    @0
    cX
    cY
    cB
    cB
    opelxpi
    3adant1
    @0
    @1
    @5
    @11
    wceq
    #
    @2
    @0
    cK
    cpo
    wcel
    #
    cK
    cjn
    cfv
    #
    cdm
    @11
    wceq
    #
    @12
    wa
    wa
    @12
    cB
    @14
    cK
    c.an
    latmcom.b
    @14
    eqid
    latmcom.m
    islat
    @13
    @15
    @12
    simprr
    sylbi
    3ad2ant1
    #
    eleqtrrd
    @3
    @7
    @11
    @5
    @1
    @2
    @7
    @11
    wcel
    #
    @0
    @2
    @1
    @17
    cY
    cX
    cB
    cB
    opelxpi
    ancoms
    3adant1
    @16
    eleqtrrd
    jca
    @0
    @13
    @1
    @2
    @9
    @10
    cK
    latpos
    cB
    cK
    c.an
    cX
    cY
    latmcom.b
    latmcom.m
    meetcom
    syl3anl1
    mpdan
end
