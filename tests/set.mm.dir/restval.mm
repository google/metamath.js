include "wcel.mm"
include "cvv.mm"
include "crest.mm"
include "co.mm"
include "cv.mm"
include "cin.mm"
include "cmpt.mm"
include "crn.mm"
include "wceq.mm"
include "elex.mm"
include "mptexg.mm"
include "rnexg.mm"
include "syl.mm"
include "adantr.mm"
include "wa.mm"
include "simpl.mm"
include "simpr.mm"
include "ineq2d.mm"
include "mpteq12dv.mm"
include "rneqd.mm"
include "df-rest.mm"
include "ovmpt2ga.mm"
include "mpd3an3.mm"
include "syl2an.mm"

theorem restval
  let vx: setvar x
  let cA: class A
  let cJ: class J
  let cV: class V
  let cW: class W
  let vj: setvar j
  let vy: setvar y
  let cB: class B
  let cS: class S

  disjoint A x
  disjoint J x
  disjoint j x
  disjoint j y
  disjoint A j
  disjoint x y
  disjoint A y
  disjoint B x
  disjoint J j
  disjoint J y
  disjoint S x
  assert |- ( ( J e. V /\ A e. W ) -> ( J |`t A ) = ran ( x e. J |-> ( x i^i A ) ) )

  proof
    cJ
    cV
    wcel
    cJ
    cvv
    wcel
    #
    cA
    cvv
    wcel
    #
    cJ
    cA
    crest
    co
    vx
    cJ
    vx
    cv
    #
    cA
    cin
    #
    cmpt
    #
    crn
    #
    wceq
    #
    cA
    cW
    wcel
    cJ
    cV
    elex
    cA
    cW
    elex
    @0
    @1
    @5
    cvv
    wcel
    #
    @6
    @0
    @7
    @1
    @0
    @4
    cvv
    wcel
    @7
    vx
    cJ
    @3
    cvv
    mptexg
    @4
    cvv
    rnexg
    syl
    adantr
    vj
    vy
    cJ
    cA
    cvv
    cvv
    vx
    vj
    cv
    #
    @2
    vy
    cv
    #
    cin
    #
    cmpt
    #
    crn
    @5
    crest
    cvv
    @8
    cJ
    wceq
    #
    @9
    cA
    wceq
    #
    wa
    #
    @11
    @4
    @14
    vx
    @8
    @10
    cJ
    @3
    @12
    @13
    simpl
    @14
    @9
    cA
    @2
    @12
    @13
    simpr
    ineq2d
    mpteq12dv
    rneqd
    vy
    vx
    vj
    df-rest
    ovmpt2ga
    mpd3an3
    syl2an
end
