include "wcel.mm"
include "cpw.mm"
include "wss.mm"
include "wa.mm"
include "crest.mm"
include "co.mm"
include "cv.mm"
include "cin.mm"
include "cmpt.mm"
include "crn.mm"
include "cvv.mm"
include "wceq.mm"
include "pwexg.mm"
include "adantr.mm"
include "simpr.mm"
include "ssexd.mm"
include "simpl.mm"
include "restval.mm"
include "syl2anc.mm"
include "cid.mm"
include "cres.mm"
include "sselda.mm"
include "elpwid.mm"
include "df-ss.mm"
include "sylib.mm"
include "mpteq2dva.mm"
include "mptresid.mm"
include "syl6eq.mm"
include "rneqd.mm"
include "rnresi.mm"
include "eqtrd.mm"

theorem restid2
  let cA: class A
  let cJ: class J
  let cV: class V
  let vf: setvar f
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( ( A e. V /\ J C_ ~P A ) -> ( J |`t A ) = J )

  proof
    cA
    cV
    wcel
    #
    cJ
    cA
    cpw
    #
    wss
    #
    wa
    #
    cJ
    cA
    crest
    co
    #
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
    cJ
    @3
    cJ
    cvv
    wcel
    @0
    @4
    @8
    wceq
    @3
    cJ
    @1
    cvv
    @0
    @1
    cvv
    wcel
    @2
    cA
    cV
    pwexg
    adantr
    @0
    @2
    simpr
    #
    ssexd
    @0
    @2
    simpl
    vx
    cA
    cJ
    cvv
    cV
    restval
    syl2anc
    @3
    @8
    cid
    cJ
    cres
    #
    crn
    cJ
    @3
    @7
    @10
    @3
    @7
    vx
    cJ
    @5
    cmpt
    @10
    @3
    vx
    cJ
    @6
    @5
    @3
    @5
    cJ
    wcel
    wa
    #
    @5
    cA
    wss
    @6
    @5
    wceq
    @11
    @5
    cA
    @3
    cJ
    @1
    @5
    @9
    sselda
    elpwid
    @5
    cA
    df-ss
    sylib
    mpteq2dva
    vx
    cJ
    mptresid
    syl6eq
    rneqd
    cJ
    rnresi
    syl6eq
    eqtrd
end
