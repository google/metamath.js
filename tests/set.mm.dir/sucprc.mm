include "cvv.mm"
include "wcel.mm"
include "wn.mm"
include "csn.mm"
include "cun.mm"
include "c0.mm"
include "csuc.mm"
include "wceq.mm"
include "snprc.mm"
include "biimpi.mm"
include "uneq2d.mm"
include "df-suc.mm"
include "un0.mm"
include "eqcomi.mm"
include "3eqtr4g.mm"

theorem sucprc
  let cA: class A


  assert |- ( -. A e. _V -> suc A = A )

  proof
    cA
    cvv
    wcel
    wn
    #
    cA
    cA
    csn
    #
    cun
    cA
    c0
    cun
    #
    cA
    csuc
    cA
    @0
    @1
    c0
    cA
    @0
    @1
    c0
    wceq
    cA
    snprc
    biimpi
    uneq2d
    cA
    df-suc
    @2
    cA
    cA
    un0
    eqcomi
    3eqtr4g
end
