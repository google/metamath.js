include "cv.mm"
include "wceq.mm"
include "wi.mm"
include "wal.mm"
include "csb.mm"
include "eqeq2.mm"
include "imbi1d.mm"
include "albidv.mm"
include "csbeq1.mm"
include "eqeq1d.mm"
include "vex.mm"
include "csbieb.mm"
include "vtoclbg.mm"

theorem csbiebg
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cV: class V
  let va: setvar a
  assume csbiebg.2: |- F/_ x C

  disjoint A x
  disjoint a x
  disjoint A a
  disjoint B a
  disjoint C a
  assert |- ( A e. V -> ( A. x ( x = A -> B = C ) <-> [_ A / x ]_ B = C ) )

  proof
    vx
    cv
    #
    va
    cv
    #
    wceq
    #
    cB
    cC
    wceq
    #
    wi
    #
    vx
    wal
    vx
    @1
    cB
    csb
    #
    cC
    wceq
    @0
    cA
    wceq
    #
    @3
    wi
    #
    vx
    wal
    vx
    cA
    cB
    csb
    #
    cC
    wceq
    va
    cA
    cV
    @1
    cA
    wceq
    #
    @4
    @7
    vx
    @9
    @2
    @6
    @3
    @1
    cA
    @0
    eqeq2
    imbi1d
    albidv
    @9
    @5
    @8
    cC
    vx
    @1
    cA
    cB
    csbeq1
    eqeq1d
    vx
    @1
    cB
    cC
    va
    vex
    csbiebg.2
    csbieb
    vtoclbg
end
