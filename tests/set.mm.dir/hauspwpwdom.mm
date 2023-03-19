include "cha.mm"
include "wcel.mm"
include "wss.mm"
include "wa.mm"
include "ccl.mm"
include "cfv.mm"
include "cvv.mm"
include "cpw.mm"
include "cv.mm"
include "cin.mm"
include "wceq.mm"
include "wrex.mm"
include "cab.mm"
include "cmpt.mm"
include "wf1.mm"
include "cdom.mm"
include "wbr.mm"
include "fvexd.mm"
include "ctop.mm"
include "haustop.mm"
include "topopn.mm"
include "syl.mm"
include "adantr.mm"
include "simpr.mm"
include "ssexd.mm"
include "pwexg.mm"
include "3syl.mm"
include "eqid.mm"
include "hauspwpwf1.mm"
include "f1dom2g.mm"
include "syl3anc.mm"

theorem hauspwpwdom
  let cA: class A
  let cJ: class J
  let cX: class X
  let va: setvar a
  let vj: setvar j
  let vk: setvar k
  let vl: setvar l
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume hauspwpwf1.x: |- X = U. J


  assert |- ( ( J e. Haus /\ A C_ X ) -> ( ( cls ` J ) ` A ) ~<_ ~P ~P A )

  proof
    cJ
    cha
    wcel
    #
    cA
    cX
    wss
    #
    wa
    #
    cA
    cJ
    ccl
    cfv
    #
    cfv
    #
    cvv
    wcel
    cA
    cpw
    #
    cpw
    #
    cvv
    wcel
    #
    @4
    @6
    vx
    @4
    vx
    cv
    vy
    cv
    #
    wcel
    vz
    cv
    @8
    cA
    cin
    wceq
    wa
    vy
    cJ
    wrex
    vz
    cab
    cmpt
    #
    wf1
    @4
    @6
    cdom
    wbr
    @2
    cA
    @3
    fvexd
    @2
    cA
    cvv
    wcel
    @5
    cvv
    wcel
    @7
    @2
    cA
    cX
    cJ
    @0
    cX
    cJ
    wcel
    #
    @1
    @0
    cJ
    ctop
    wcel
    @10
    cJ
    haustop
    cJ
    cX
    hauspwpwf1.x
    topopn
    syl
    adantr
    @0
    @1
    simpr
    ssexd
    cA
    cvv
    pwexg
    @5
    cvv
    pwexg
    3syl
    vx
    cA
    vy
    @9
    cJ
    cX
    vz
    hauspwpwf1.x
    @9
    eqid
    hauspwpwf1
    @4
    @6
    @9
    cvv
    cvv
    f1dom2g
    syl3anc
end
