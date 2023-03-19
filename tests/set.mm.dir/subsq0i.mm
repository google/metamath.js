include "c2.mm"
include "cexp.mm"
include "co.mm"
include "cmin.mm"
include "cc0.mm"
include "wceq.mm"
include "cneg.mm"
include "wo.mm"
include "sqcli.mm"
include "subeq0i.mm"
include "sqeqori.mm"
include "bitri.mm"

theorem subsq0i
  let cA: class A
  let cB: class B
  assume binom2.1: |- A e. CC
  assume binom2.2: |- B e. CC


  assert |- ( ( ( A ^ 2 ) - ( B ^ 2 ) ) = 0 <-> ( A = B \/ A = -u B ) )

  proof
    cA
    c2
    cexp
    co
    #
    cB
    c2
    cexp
    co
    #
    cmin
    co
    cc0
    wceq
    @0
    @1
    wceq
    cA
    cB
    wceq
    cA
    cB
    cneg
    wceq
    wo
    @0
    @1
    cA
    binom2.1
    sqcli
    cB
    binom2.2
    sqcli
    subeq0i
    cA
    cB
    binom2.1
    binom2.2
    sqeqori
    bitri
end
