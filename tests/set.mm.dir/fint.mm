include "wfn.mm"
include "crn.mm"
include "cint.mm"
include "wss.mm"
include "wa.mm"
include "cv.mm"
include "wral.mm"
include "wf.mm"
include "ssint.mm"
include "anbi2i.mm"
include "c0.mm"
include "wne.mm"
include "wb.mm"
include "r19.28zv.mm"
include "ax-mp.mm"
include "bitr4i.mm"
include "df-f.mm"
include "ralbii.mm"
include "3bitr4i.mm"

theorem fint
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cF: class F
  assume fint.1: |- B =/= (/)

  disjoint A x
  disjoint B x
  disjoint F x
  assert |- ( F : A --> |^| B <-> A. x e. B F : A --> x )

  proof
    cF
    cA
    wfn
    #
    cF
    crn
    #
    cB
    cint
    #
    wss
    #
    wa
    #
    @0
    @1
    vx
    cv
    #
    wss
    #
    wa
    #
    vx
    cB
    wral
    #
    cA
    @2
    cF
    wf
    cA
    @5
    cF
    wf
    #
    vx
    cB
    wral
    @4
    @0
    @6
    vx
    cB
    wral
    #
    wa
    #
    @8
    @3
    @10
    @0
    vx
    @1
    cB
    ssint
    anbi2i
    cB
    c0
    wne
    @8
    @11
    wb
    fint.1
    @0
    @6
    vx
    cB
    r19.28zv
    ax-mp
    bitr4i
    cA
    @2
    cF
    df-f
    @9
    @7
    vx
    cB
    cA
    @5
    cF
    df-f
    ralbii
    3bitr4i
end
