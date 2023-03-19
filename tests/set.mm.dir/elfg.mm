include "cfbas.mm"
include "cfv.mm"
include "wcel.mm"
include "cfg.mm"
include "co.mm"
include "cv.mm"
include "cpw.mm"
include "cin.mm"
include "c0.mm"
include "wne.mm"
include "crab.mm"
include "wss.mm"
include "wrex.mm"
include "wa.mm"
include "fgval.mm"
include "eleq2d.mm"
include "wceq.mm"
include "pweq.mm"
include "ineq2d.mm"
include "neeq1d.mm"
include "elrab.mm"
include "cdm.mm"
include "wb.mm"
include "elfvdm.mm"
include "elpw2g.mm"
include "syl.mm"
include "wex.mm"
include "elin.mm"
include "selpw.mm"
include "anbi2i.mm"
include "bitri.mm"
include "exbii.mm"
include "n0.mm"
include "df-rex.mm"
include "3bitr4i.mm"
include "a1i.mm"
include "anbi12d.mm"
include "syl5bb.mm"
include "bitrd.mm"

theorem elfg
  let vx: setvar x
  let cA: class A
  let cF: class F
  let cX: class X
  let vy: setvar y

  disjoint A x
  disjoint F x
  disjoint x y
  disjoint A y
  disjoint F y
  disjoint X y
  assert |- ( F e. ( fBas ` X ) -> ( A e. ( X filGen F ) <-> ( A C_ X /\ E. x e. F x C_ A ) ) )

  proof
    cF
    cX
    cfbas
    cfv
    wcel
    #
    cA
    cX
    cF
    cfg
    co
    #
    wcel
    cA
    cF
    vy
    cv
    #
    cpw
    #
    cin
    #
    c0
    wne
    #
    vy
    cX
    cpw
    #
    crab
    #
    wcel
    #
    cA
    cX
    wss
    #
    vx
    cv
    #
    cA
    wss
    #
    vx
    cF
    wrex
    #
    wa
    #
    @0
    @1
    @7
    cA
    vy
    cF
    cX
    fgval
    eleq2d
    @8
    cA
    @6
    wcel
    #
    cF
    cA
    cpw
    #
    cin
    #
    c0
    wne
    #
    wa
    @0
    @13
    @5
    @17
    vy
    cA
    @6
    @2
    cA
    wceq
    #
    @4
    @16
    c0
    @18
    @3
    @15
    cF
    @2
    cA
    pweq
    ineq2d
    neeq1d
    elrab
    @0
    @14
    @9
    @17
    @12
    @0
    cX
    cfbas
    cdm
    #
    wcel
    @14
    @9
    wb
    cF
    cX
    cfbas
    elfvdm
    cA
    cX
    @19
    elpw2g
    syl
    @17
    @12
    wb
    @0
    @10
    @16
    wcel
    #
    vx
    wex
    @10
    cF
    wcel
    #
    @11
    wa
    #
    vx
    wex
    @17
    @12
    @20
    @22
    vx
    @20
    @21
    @10
    @15
    wcel
    #
    wa
    @22
    @10
    cF
    @15
    elin
    @23
    @11
    @21
    vx
    cA
    selpw
    anbi2i
    bitri
    exbii
    vx
    @16
    n0
    @11
    vx
    cF
    df-rex
    3bitr4i
    a1i
    anbi12d
    syl5bb
    bitrd
end
