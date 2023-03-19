include "wcel.mm"
include "cv.mm"
include "wf.mm"
include "con0.mm"
include "wrex.mm"
include "cfv.mm"
include "c0.mm"
include "csn.mm"
include "cun.mm"
include "wceq.mm"
include "feq1.mm"
include "rexbidv.mm"
include "elab2g.mm"
include "ibi.mm"
include "crn.mm"
include "wss.mm"
include "frn.mm"
include "unss1.mm"
include "syl.mm"
include "fvrn0.mm"
include "ssel.mm"
include "mpisyl.mm"
include "rexlimivw.mm"

theorem orderseqlem
  let vx: setvar x
  let cA: class A
  let vf: setvar f
  let cF: class F
  let cG: class G
  let cX: class X
  assume orderseqlem.1: |- F = { f | E. x e. On f : x --> A }

  disjoint A f
  disjoint A x
  disjoint f x
  disjoint G f
  disjoint G x
  disjoint X x
  assert |- ( G e. F -> ( G ` X ) e. ( A u. { (/) } ) )

  proof
    cG
    cF
    wcel
    #
    vx
    cv
    #
    cA
    cG
    wf
    #
    vx
    con0
    wrex
    #
    cX
    cG
    cfv
    #
    cA
    c0
    csn
    #
    cun
    #
    wcel
    #
    @0
    @3
    @1
    cA
    vf
    cv
    #
    wf
    #
    vx
    con0
    wrex
    @3
    vf
    cG
    cF
    cF
    @8
    cG
    wceq
    @9
    @2
    vx
    con0
    @1
    cA
    @8
    cG
    feq1
    rexbidv
    orderseqlem.1
    elab2g
    ibi
    @2
    @7
    vx
    con0
    @2
    cG
    crn
    #
    @5
    cun
    #
    @6
    wss
    #
    @4
    @11
    wcel
    @7
    @2
    @10
    cA
    wss
    @12
    @1
    cA
    cG
    frn
    @10
    cA
    @5
    unss1
    syl
    cG
    cX
    fvrn0
    @11
    @6
    @4
    ssel
    mpisyl
    rexlimivw
    syl
end
