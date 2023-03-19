include "chil.mm"
include "wss.mm"
include "wa.mm"
include "cort.mm"
include "cfv.mm"
include "ococss.mm"
include "adantl.mm"
include "wi.mm"
include "ocss.mm"
include "occon.mm"
include "sylan2.mm"
include "sstr2.mm"
include "sylsyld.mm"
include "adantr.mm"
include "id.mm"
include "syl2anr.mm"
include "impbid.mm"

theorem occon3
  let cA: class A
  let cB: class B
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cH: class H


  assert |- ( ( A C_ ~H /\ B C_ ~H ) -> ( A C_ ( _|_ ` B ) <-> B C_ ( _|_ ` A ) ) )

  proof
    cA
    chil
    wss
    #
    cB
    chil
    wss
    #
    wa
    #
    cA
    cB
    cort
    cfv
    #
    wss
    #
    cB
    cA
    cort
    cfv
    #
    wss
    #
    @2
    cB
    @3
    cort
    cfv
    #
    wss
    #
    @4
    @7
    @5
    wss
    #
    @6
    @1
    @8
    @0
    cB
    ococss
    adantl
    @1
    @0
    @3
    chil
    wss
    @4
    @9
    wi
    cB
    ocss
    cA
    @3
    occon
    sylan2
    cB
    @7
    @5
    sstr2
    sylsyld
    @2
    cA
    @5
    cort
    cfv
    #
    wss
    #
    @6
    @10
    @3
    wss
    #
    @4
    @0
    @11
    @1
    cA
    ococss
    adantr
    @1
    @1
    @5
    chil
    wss
    @6
    @12
    wi
    @0
    @1
    id
    cA
    ocss
    cB
    @5
    occon
    syl2anr
    cA
    @10
    @3
    sstr2
    sylsyld
    impbid
end
