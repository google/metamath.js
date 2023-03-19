include "crp.mm"
include "wcel.mm"
include "c1.mm"
include "wne.mm"
include "w3a.mm"
include "clog.mm"
include "cfv.mm"
include "cr.mm"
include "relogcl.mm"
include "3ad2ant1.mm"
include "3ad2ant2.mm"
include "cc0.mm"
include "logne0.mm"
include "3adant1.mm"
include "redivcld.mm"

theorem reglogcl
  let cA: class A
  let cB: class B


  assert |- ( ( A e. RR+ /\ B e. RR+ /\ B =/= 1 ) -> ( ( log ` A ) / ( log ` B ) ) e. RR )

  proof
    cA
    crp
    wcel
    #
    cB
    crp
    wcel
    #
    cB
    c1
    wne
    #
    w3a
    cA
    clog
    cfv
    #
    cB
    clog
    cfv
    #
    @0
    @1
    @3
    cr
    wcel
    @2
    cA
    relogcl
    3ad2ant1
    @1
    @0
    @4
    cr
    wcel
    @2
    cB
    relogcl
    3ad2ant2
    @1
    @2
    @4
    cc0
    wne
    @0
    cB
    logne0
    3adant1
    redivcld
end
