include "chil.mm"
include "wcel.mm"
include "csp.mm"
include "co.mm"
include "cr.mm"
include "wa.mm"
include "wceq.mm"
include "eqid.mm"
include "hire.mm"
include "mpbiri.mm"
include "anidms.mm"

theorem hiidrcl
  let cA: class A


  assert |- ( A e. ~H -> ( A .ih A ) e. RR )

  proof
    cA
    chil
    wcel
    #
    cA
    cA
    csp
    co
    #
    cr
    wcel
    #
    @0
    @0
    wa
    @2
    @1
    @1
    wceq
    @1
    eqid
    cA
    cA
    hire
    mpbiri
    anidms
end
