include "con0.mm"
include "c1o.mm"
include "cdif.mm"
include "wcel.mm"
include "c0.mm"
include "wne.mm"
include "wa.mm"
include "dif1o.mm"
include "on0eln0.mm"
include "pm5.32i.mm"
include "bitr4i.mm"

theorem ondif1
  let cA: class A


  assert |- ( A e. ( On \ 1o ) <-> ( A e. On /\ (/) e. A ) )

  proof
    cA
    con0
    c1o
    cdif
    wcel
    cA
    con0
    wcel
    #
    cA
    c0
    wne
    #
    wa
    @0
    c0
    cA
    wcel
    #
    wa
    cA
    con0
    dif1o
    @0
    @2
    @1
    cA
    on0eln0
    pm5.32i
    bitr4i
end
