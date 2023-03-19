include "wcel.mm"
include "cn0.mm"
include "wa.mm"
include "cvv.mm"
include "cc0.mm"
include "cfzo.mm"
include "co.mm"
include "cmpt.mm"
include "creps.mm"
include "wceq.mm"
include "elex.mm"
include "adantr.mm"
include "simpr.mm"
include "ovex.mm"
include "mptexg.mm"
include "mp1i.mm"
include "cv.mm"
include "oveq2.mm"
include "adantl.mm"
include "simpll.mm"
include "mpteq12dva.mm"
include "df-reps.mm"
include "ovmpt2ga.mm"
include "syl3anc.mm"

theorem reps
  let vx: setvar x
  let cS: class S
  let cN: class N
  let cV: class V
  let vn: setvar n
  let vs: setvar s

  disjoint N x
  disjoint S x
  disjoint N n
  disjoint N s
  disjoint n s
  disjoint n x
  disjoint s x
  disjoint S n
  disjoint S s
  assert |- ( ( S e. V /\ N e. NN0 ) -> ( S repeatS N ) = ( x e. ( 0 ..^ N ) |-> S ) )

  proof
    cS
    cV
    wcel
    #
    cN
    cn0
    wcel
    #
    wa
    #
    cS
    cvv
    wcel
    #
    @1
    vx
    cc0
    cN
    cfzo
    co
    #
    cS
    cmpt
    #
    cvv
    wcel
    #
    cS
    cN
    creps
    co
    @5
    wceq
    @0
    @3
    @1
    cS
    cV
    elex
    adantr
    @0
    @1
    simpr
    @4
    cvv
    wcel
    @6
    @2
    cc0
    cN
    cfzo
    ovex
    vx
    @4
    cS
    cvv
    mptexg
    mp1i
    vs
    vn
    cS
    cN
    cvv
    cn0
    vx
    cc0
    vn
    cv
    #
    cfzo
    co
    #
    vs
    cv
    #
    cmpt
    @5
    creps
    cvv
    @9
    cS
    wceq
    #
    @7
    cN
    wceq
    #
    wa
    vx
    @8
    @9
    @4
    cS
    @11
    @8
    @4
    wceq
    @10
    @7
    cN
    cc0
    cfzo
    oveq2
    adantl
    @10
    @11
    vx
    cv
    @8
    wcel
    simpll
    mpteq12dva
    vx
    vn
    vs
    df-reps
    ovmpt2ga
    syl3anc
end
