include "wf1.mm"
include "wf.mm"
include "ccnv.mm"
include "wfun.mm"
include "wa.mm"
include "cv.mm"
include "wbr.mm"
include "wmo.mm"
include "wal.mm"
include "df-f1.mm"
include "funcnv2.mm"
include "anbi2i.mm"
include "bitri.mm"

theorem dff12
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cF: class F

  disjoint x y
  disjoint F x
  disjoint F y
  assert |- ( F : A -1-1-> B <-> ( F : A --> B /\ A. y E* x x F y ) )

  proof
    cA
    cB
    cF
    wf1
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
    @0
    vx
    cv
    vy
    cv
    cF
    wbr
    vx
    wmo
    vy
    wal
    #
    wa
    cA
    cB
    cF
    df-f1
    @1
    @2
    @0
    vx
    vy
    cF
    funcnv2
    anbi2i
    bitri
end
