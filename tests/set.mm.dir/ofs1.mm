include "wcel.mm"
include "wa.mm"
include "cs1.mm"
include "cof.mm"
include "co.mm"
include "cc0.mm"
include "csn.mm"
include "cmpt.mm"
include "cvv.mm"
include "snex.mm"
include "a1i.mm"
include "cv.mm"
include "simpll.mm"
include "simplr.mm"
include "wceq.mm"
include "cop.mm"
include "s1val.mm"
include "cn0.mm"
include "0nn0.mm"
include "fmptsn.mm"
include "mpan.mm"
include "eqtrd.mm"
include "adantr.mm"
include "adantl.mm"
include "offval2.mm"
include "ovex.mm"
include "ax-mp.mm"
include "mp2an.mm"
include "eqtri.mm"
include "syl6eqr.mm"

theorem ofs1
  let cA: class A
  let cB: class B
  let cR: class R
  let cS: class S
  let cT: class T
  let vi: setvar i


  assert |- ( ( A e. S /\ B e. T ) -> ( <" A "> oF R <" B "> ) = <" ( A R B ) "> )

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
    cs1
    #
    cR
    cof
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
    @6
    cs1
    #
    @2
    vi
    @5
    cA
    cB
    cR
    @3
    @4
    cvv
    cS
    cT
    @5
    cvv
    wcel
    @2
    cc0
    snex
    a1i
    @0
    @1
    vi
    cv
    @5
    wcel
    #
    simpll
    @0
    @1
    @9
    simplr
    @0
    @3
    vi
    @5
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
    @10
    cA
    cS
    s1val
    cc0
    cn0
    wcel
    #
    @0
    @11
    @10
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
    @1
    @4
    vi
    @5
    cB
    cmpt
    #
    wceq
    @0
    @1
    @4
    cc0
    cB
    cop
    csn
    #
    @13
    cB
    cT
    s1val
    @12
    @1
    @14
    @13
    wceq
    0nn0
    vi
    cc0
    cB
    cn0
    cT
    fmptsn
    mpan
    eqtrd
    adantl
    offval2
    @8
    cc0
    @6
    cop
    csn
    #
    @7
    @6
    cvv
    wcel
    #
    @8
    @15
    wceq
    cA
    cB
    cR
    ovex
    #
    @6
    cvv
    s1val
    ax-mp
    @12
    @16
    @15
    @7
    wceq
    0nn0
    @17
    vi
    cc0
    @6
    cn0
    cvv
    fmptsn
    mp2an
    eqtri
    syl6eqr
end
