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
include "cmee.mm"
include "cfv.mm"
include "eqid.mm"
include "islat.mm"
include "simprl.mm"
include "sylbi.mm"
include "3ad2ant1.mm"
include "eleqtrrd.mm"
include "ancoms.mm"
include "jca.mm"
include "latpos.mm"
include "joincom.mm"
include "syl3anl1.mm"
include "mpdan.mm"

theorem latjcom
  let cB: class B
  let c.or: class .\/
  let cK: class K
  let cX: class X
  let cY: class Y
  assume latjcom.b: |- B = ( Base ` K )
  assume latjcom.j: |- .\/ = ( join ` K )


  assert |- ( ( K e. Lat /\ X e. B /\ Y e. B ) -> ( X .\/ Y ) = ( Y .\/ X ) )

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
    c.or
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
    c.or
    co
    cY
    cX
    c.or
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
    @12
    cK
    cmee
    cfv
    #
    cdm
    @11
    wceq
    #
    wa
    wa
    @12
    cB
    c.or
    cK
    @14
    latjcom.b
    latjcom.j
    @14
    eqid
    islat
    @13
    @12
    @15
    simprl
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
    c.or
    cK
    cX
    cY
    latjcom.b
    latjcom.j
    joincom
    syl3anl1
    mpdan
end
