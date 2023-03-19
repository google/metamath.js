include "wss.mm"
include "cc.mm"
include "wa.mm"
include "ccncf.mm"
include "co.mm"
include "cv.mm"
include "wcel.mm"
include "wf.mm"
include "cncff.mm"
include "adantl.mm"
include "simpll.mm"
include "fssd.mm"
include "wb.mm"
include "cncffvrn.mm"
include "adantll.mm"
include "mpbird.mm"
include "ex.mm"
include "ssrdv.mm"

theorem cncfss
  let cA: class A
  let cB: class B
  let cC: class C
  let vf: setvar f
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cF: class F


  assert |- ( ( B C_ C /\ C C_ CC ) -> ( A -cn-> B ) C_ ( A -cn-> C ) )

  proof
    cB
    cC
    wss
    #
    cC
    cc
    wss
    #
    wa
    #
    vf
    cA
    cB
    ccncf
    co
    #
    cA
    cC
    ccncf
    co
    #
    @2
    vf
    cv
    #
    @3
    wcel
    #
    @5
    @4
    wcel
    #
    @2
    @6
    wa
    #
    @7
    cA
    cC
    @5
    wf
    #
    @8
    cA
    cB
    cC
    @5
    @6
    cA
    cB
    @5
    wf
    @2
    cA
    cB
    @5
    cncff
    adantl
    @0
    @1
    @6
    simpll
    fssd
    @1
    @6
    @7
    @9
    wb
    @0
    cA
    cB
    cC
    @5
    cncffvrn
    adantll
    mpbird
    ex
    ssrdv
end
