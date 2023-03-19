include "wcel.mm"
include "w3a.mm"
include "cpr.mm"
include "club.mm"
include "cfv.mm"
include "co.mm"
include "wceq.mm"
include "prcom.mm"
include "fveq2i.mm"
include "a1i.mm"
include "eqid.mm"
include "simp1.mm"
include "simp3.mm"
include "simp2.mm"
include "joinval.mm"
include "3eqtr4rd.mm"

theorem joincomALT
  let cB: class B
  let c.or: class .\/
  let cK: class K
  let cV: class V
  let cX: class X
  let cY: class Y
  assume joincom.b: |- B = ( Base ` K )
  assume joincom.j: |- .\/ = ( join ` K )


  assert |- ( ( K e. V /\ X e. B /\ Y e. B ) -> ( X .\/ Y ) = ( Y .\/ X ) )

  proof
    cK
    cV
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
    cY
    cX
    cpr
    #
    cK
    club
    cfv
    #
    cfv
    #
    cX
    cY
    cpr
    #
    @5
    cfv
    #
    cY
    cX
    c.or
    co
    cX
    cY
    c.or
    co
    @6
    @8
    wceq
    @3
    @4
    @7
    @5
    cY
    cX
    prcom
    fveq2i
    a1i
    @3
    @5
    c.or
    cK
    cV
    cB
    cY
    cX
    cB
    @5
    eqid
    #
    joincom.j
    @0
    @1
    @2
    simp1
    #
    @0
    @1
    @2
    simp3
    #
    @0
    @1
    @2
    simp2
    #
    joinval
    @3
    @5
    c.or
    cK
    cV
    cB
    cX
    cY
    cB
    @9
    joincom.j
    @10
    @12
    @11
    joinval
    3eqtr4rd
end
