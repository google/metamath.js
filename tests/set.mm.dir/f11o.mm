include "wf.mm"
include "ccnv.mm"
include "wfun.mm"
include "wa.mm"
include "cv.mm"
include "wfo.mm"
include "wss.mm"
include "wex.mm"
include "wf1.mm"
include "wf1o.mm"
include "ffoss.mm"
include "anbi1i.mm"
include "df-f1.mm"
include "dff1o3.mm"
include "an32.mm"
include "bitri.mm"
include "exbii.mm"
include "19.41v.mm"
include "3bitr4i.mm"

theorem f11o
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cF: class F
  assume f11o.1: |- F e. _V

  disjoint F x
  disjoint A x
  disjoint B x
  assert |- ( F : A -1-1-> B <-> E. x ( F : A -1-1-onto-> x /\ x C_ B ) )

  proof
    cA
    cB
    cF
    wf
    #
    cF
    ccnv
    wfun
    #
    wa
    cA
    vx
    cv
    #
    cF
    wfo
    #
    @2
    cB
    wss
    #
    wa
    #
    vx
    wex
    #
    @1
    wa
    #
    cA
    cB
    cF
    wf1
    cA
    @2
    cF
    wf1o
    #
    @4
    wa
    #
    vx
    wex
    #
    @0
    @6
    @1
    vx
    cA
    cB
    cF
    f11o.1
    ffoss
    anbi1i
    cA
    cB
    cF
    df-f1
    @10
    @5
    @1
    wa
    #
    vx
    wex
    @7
    @9
    @11
    vx
    @9
    @3
    @1
    wa
    #
    @4
    wa
    @11
    @8
    @12
    @4
    cA
    @2
    cF
    dff1o3
    anbi1i
    @3
    @1
    @4
    an32
    bitri
    exbii
    @5
    @1
    vx
    19.41v
    bitri
    3bitr4i
end
