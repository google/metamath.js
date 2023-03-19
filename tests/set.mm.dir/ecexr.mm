include "cvv.mm"
include "wcel.mm"
include "csn.mm"
include "cima.mm"
include "cec.mm"
include "c0.mm"
include "wceq.mm"
include "n0i.mm"
include "wn.mm"
include "snprc.mm"
include "imaeq2.mm"
include "sylbi.mm"
include "ima0.mm"
include "syl6eq.mm"
include "nsyl2.mm"
include "df-ec.mm"
include "eleq2s.mm"

theorem ecexr
  let cA: class A
  let cB: class B
  let cR: class R


  assert |- ( A e. [ B ] R -> B e. _V )

  proof
    cB
    cvv
    wcel
    #
    cA
    cR
    cB
    csn
    #
    cima
    #
    cB
    cR
    cec
    cA
    @2
    wcel
    @2
    c0
    wceq
    @0
    @2
    cA
    n0i
    @0
    wn
    #
    @2
    cR
    c0
    cima
    #
    c0
    @3
    @1
    c0
    wceq
    @2
    @4
    wceq
    cB
    snprc
    @1
    c0
    cR
    imaeq2
    sylbi
    cR
    ima0
    syl6eq
    nsyl2
    cB
    cR
    df-ec
    eleq2s
end
