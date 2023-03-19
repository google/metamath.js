include "crest.mm"
include "co.mm"
include "ctop.mm"
include "wcel.mm"
include "c0.mm"
include "wceq.mm"
include "cvv.mm"
include "wa.mm"
include "wn.mm"
include "0opn.mm"
include "n0i.mm"
include "syl.mm"
include "cxp.mm"
include "wfn.mm"
include "cdm.mm"
include "restfn.mm"
include "fndm.mm"
include "ax-mp.mm"
include "ndmov.mm"
include "nsyl2.mm"

theorem restrcl
  let cA: class A
  let cJ: class J


  assert |- ( ( J |`t A ) e. Top -> ( J e. _V /\ A e. _V ) )

  proof
    cJ
    cA
    crest
    co
    #
    ctop
    wcel
    #
    @0
    c0
    wceq
    #
    cJ
    cvv
    wcel
    cA
    cvv
    wcel
    wa
    @1
    c0
    @0
    wcel
    @2
    wn
    @0
    0opn
    @0
    c0
    n0i
    syl
    cJ
    cA
    cvv
    crest
    crest
    cvv
    cvv
    cxp
    #
    wfn
    crest
    cdm
    @3
    wceq
    restfn
    @3
    crest
    fndm
    ax-mp
    ndmov
    nsyl2
end
