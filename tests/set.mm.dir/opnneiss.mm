include "ctop.mm"
include "wcel.mm"
include "wss.mm"
include "w3a.mm"
include "cnei.mm"
include "cfv.mm"
include "simp3.mm"
include "cuni.mm"
include "wb.mm"
include "eqid.mm"
include "eltopss.mm"
include "sstr.mm"
include "ancoms.mm"
include "stoic3.mm"
include "opnneissb.mm"
include "syld3an3.mm"
include "mpbid.mm"

theorem opnneiss
  let cS: class S
  let cJ: class J
  let cN: class N


  assert |- ( ( J e. Top /\ N e. J /\ S C_ N ) -> N e. ( ( nei ` J ) ` S ) )

  proof
    cJ
    ctop
    wcel
    #
    cN
    cJ
    wcel
    #
    cS
    cN
    wss
    #
    w3a
    @2
    cN
    cS
    cJ
    cnei
    cfv
    cfv
    wcel
    #
    @0
    @1
    @2
    simp3
    @0
    @1
    @2
    cS
    cJ
    cuni
    #
    wss
    #
    @2
    @3
    wb
    @0
    @1
    cN
    @4
    wss
    #
    @2
    @5
    cN
    cJ
    @4
    @4
    eqid
    #
    eltopss
    @2
    @6
    @5
    cS
    cN
    @4
    sstr
    ancoms
    stoic3
    cS
    cJ
    cN
    @4
    @7
    opnneissb
    syld3an3
    mpbid
end
