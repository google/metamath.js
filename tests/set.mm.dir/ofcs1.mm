include "wcel.mm"
include "wa.mm"
include "cs1.mm"
include "cofc.mm"
include "co.mm"
include "cc0.mm"
include "csn.mm"
include "cmpt.mm"
include "cvv.mm"
include "snex.mm"
include "a1i.mm"
include "simpr.mm"
include "cv.mm"
include "simpll.mm"
include "wceq.mm"
include "cop.mm"
include "s1val.mm"
include "cn0.mm"
include "0nn0.mm"
include "fmptsn.mm"
include "mpan.mm"
include "eqtrd.mm"
include "adantr.mm"
include "ofcfval2.mm"
include "ovex.mm"
include "ax-mp.mm"
include "mp2an.mm"
include "eqtri.mm"
include "syl6eqr.mm"

theorem ofcs1
  let cA: class A
  let cB: class B
  let cR: class R
  let cS: class S
  let cT: class T
  let vi: setvar i


  assert |- ( ( A e. S /\ B e. T ) -> ( <" A "> oFC R B ) = <" ( A R B ) "> )

  proof
    cA
    cS
    wcel
    #
    cB
    cT
    wcel
    #
    wa
    #
    cA
    cs1
    #
    cB
    cR
    cofc
    co
    vi
    cc0
    csn
    #
    cA
    cB
    cR
    co
    #
    cmpt
    #
    @5
    cs1
    #
    @2
    vi
    @4
    cA
    cB
    cR
    @3
    cvv
    cT
    cS
    @4
    cvv
    wcel
    @2
    cc0
    snex
    a1i
    @0
    @1
    simpr
    @0
    @1
    vi
    cv
    @4
    wcel
    simpll
    @0
    @3
    vi
    @4
    cA
    cmpt
    #
    wceq
    @1
    @0
    @3
    cc0
    cA
    cop
    csn
    #
    @8
    cA
    cS
    s1val
    cc0
    cn0
    wcel
    #
    @0
    @9
    @8
    wceq
    0nn0
    vi
    cc0
    cA
    cn0
    cS
    fmptsn
    mpan
    eqtrd
    adantr
    ofcfval2
    @7
    cc0
    @5
    cop
    csn
    #
    @6
    @5
    cvv
    wcel
    #
    @7
    @11
    wceq
    cA
    cB
    cR
    ovex
    #
    @5
    cvv
    s1val
    ax-mp
    @10
    @12
    @11
    @6
    wceq
    0nn0
    @13
    vi
    cc0
    @5
    cn0
    cvv
    fmptsn
    mp2an
    eqtri
    syl6eqr
end
