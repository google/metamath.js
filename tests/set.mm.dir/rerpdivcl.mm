include "crp.mm"
include "wcel.mm"
include "cr.mm"
include "cc0.mm"
include "wne.mm"
include "wa.mm"
include "cdiv.mm"
include "co.mm"
include "rprene0.mm"
include "redivcl.mm"
include "3expb.mm"
include "sylan2.mm"

theorem rerpdivcl
  let cA: class A
  let cB: class B


  assert |- ( ( A e. RR /\ B e. RR+ ) -> ( A / B ) e. RR )

  proof
    cB
    crp
    wcel
    cA
    cr
    wcel
    #
    cB
    cr
    wcel
    #
    cB
    cc0
    wne
    #
    wa
    cA
    cB
    cdiv
    co
    cr
    wcel
    #
    cB
    rprene0
    @0
    @1
    @2
    @3
    cA
    cB
    redivcl
    3expb
    sylan2
end
