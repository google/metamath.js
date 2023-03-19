include "wceq.mm"
include "wo.mm"
include "wn.mm"
include "wi.mm"
include "wne.mm"
include "df-or.mm"
include "df-ne.mm"
include "imbi1i.mm"
include "bitr4i.mm"

theorem neor
  let wps: wff ps
  let cA: class A
  let cB: class B


  assert |- ( ( A = B \/ ps ) <-> ( A =/= B -> ps ) )

  proof
    cA
    cB
    wceq
    #
    wps
    wo
    @0
    wn
    #
    wps
    wi
    cA
    cB
    wne
    #
    wps
    wi
    @0
    wps
    df-or
    @2
    @1
    wps
    cA
    cB
    df-ne
    imbi1i
    bitr4i
end
