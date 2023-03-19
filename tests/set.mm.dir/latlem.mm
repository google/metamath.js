include "clat.mm"
include "wcel.mm"
include "w3a.mm"
include "co.mm"
include "simp1.mm"
include "simp2.mm"
include "simp3.mm"
include "cop.mm"
include "cxp.mm"
include "cdm.mm"
include "opelxpi.mm"
include "3adant1.mm"
include "wceq.mm"
include "cpo.mm"
include "wa.mm"
include "islat.mm"
include "simprl.mm"
include "sylbi.mm"
include "3ad2ant1.mm"
include "eleqtrrd.mm"
include "joincl.mm"
include "simprr.mm"
include "meetcl.mm"
include "jca.mm"

theorem latlem
  let cB: class B
  let c.or: class .\/
  let cK: class K
  let c.an: class ./\
  let cX: class X
  let cY: class Y
  assume latlem.b: |- B = ( Base ` K )
  assume latlem.j: |- .\/ = ( join ` K )
  assume latlem.m: |- ./\ = ( meet ` K )


  assert |- ( ( K e. Lat /\ X e. B /\ Y e. B ) -> ( ( X .\/ Y ) e. B /\ ( X ./\ Y ) e. B ) )

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
    c.or
    co
    cB
    wcel
    cX
    cY
    c.an
    co
    cB
    wcel
    @3
    cB
    c.or
    cK
    clat
    cX
    cY
    latlem.b
    latlem.j
    @0
    @1
    @2
    simp1
    #
    @0
    @1
    @2
    simp2
    #
    @0
    @1
    @2
    simp3
    #
    @3
    cX
    cY
    cop
    #
    cB
    cB
    cxp
    #
    c.or
    cdm
    #
    @1
    @2
    @7
    @8
    wcel
    @0
    cX
    cY
    cB
    cB
    opelxpi
    3adant1
    #
    @0
    @1
    @9
    @8
    wceq
    #
    @2
    @0
    cK
    cpo
    wcel
    #
    @11
    c.an
    cdm
    #
    @8
    wceq
    #
    wa
    wa
    #
    @11
    cB
    c.or
    cK
    c.an
    latlem.b
    latlem.j
    latlem.m
    islat
    #
    @12
    @11
    @14
    simprl
    sylbi
    3ad2ant1
    eleqtrrd
    joincl
    @3
    cB
    cK
    c.an
    clat
    cX
    cY
    latlem.b
    latlem.m
    @4
    @5
    @6
    @3
    @7
    @8
    @13
    @10
    @0
    @1
    @14
    @2
    @0
    @15
    @14
    @16
    @12
    @11
    @14
    simprr
    sylbi
    3ad2ant1
    eleqtrrd
    meetcl
    jca
end
