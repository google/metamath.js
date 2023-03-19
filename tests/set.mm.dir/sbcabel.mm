include "wcel.mm"
include "cvv.mm"
include "cab.mm"
include "wsbc.mm"
include "wb.mm"
include "elex.mm"
include "cv.mm"
include "wceq.mm"
include "wa.mm"
include "wex.mm"
include "sbcex2.mm"
include "sbcan.mm"
include "wal.mm"
include "sbcal.mm"
include "sbcbig.mm"
include "sbcg.mm"
include "bibi1d.mm"
include "bitrd.mm"
include "albidv.mm"
include "syl5bb.mm"
include "abeq2.mm"
include "sbcbii.mm"
include "3bitr4g.mm"
include "nfcri.mm"
include "sbcgf.mm"
include "anbi12d.mm"
include "exbidv.mm"
include "df-clel.mm"
include "syl.mm"

theorem sbcabel
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cV: class V
  let vw: setvar w
  assume sbcabel.1: |- F/_ x B

  disjoint A y
  disjoint x y
  disjoint w y
  disjoint A w
  disjoint B w
  disjoint ph w
  disjoint w x
  assert |- ( A e. V -> ( [. A / x ]. { y | ph } e. B <-> { y | [. A / x ]. ph } e. B ) )

  proof
    cA
    cV
    wcel
    cA
    cvv
    wcel
    #
    wph
    vy
    cab
    #
    cB
    wcel
    #
    vx
    cA
    wsbc
    #
    wph
    vx
    cA
    wsbc
    #
    vy
    cab
    #
    cB
    wcel
    #
    wb
    cA
    cV
    elex
    @0
    vw
    cv
    #
    @1
    wceq
    #
    @7
    cB
    wcel
    #
    wa
    #
    vw
    wex
    #
    vx
    cA
    wsbc
    #
    @7
    @5
    wceq
    #
    @9
    wa
    #
    vw
    wex
    #
    @3
    @6
    @12
    @10
    vx
    cA
    wsbc
    #
    vw
    wex
    @0
    @15
    @10
    vw
    vx
    cA
    sbcex2
    @0
    @16
    @14
    vw
    @16
    @8
    vx
    cA
    wsbc
    #
    @9
    vx
    cA
    wsbc
    #
    wa
    @0
    @14
    @8
    @9
    vx
    cA
    sbcan
    @0
    @17
    @13
    @18
    @9
    @0
    vy
    cv
    @7
    wcel
    #
    wph
    wb
    #
    vy
    wal
    #
    vx
    cA
    wsbc
    #
    @19
    @4
    wb
    #
    vy
    wal
    #
    @17
    @13
    @22
    @20
    vx
    cA
    wsbc
    #
    vy
    wal
    @0
    @24
    @20
    vy
    vx
    cA
    sbcal
    @0
    @25
    @23
    vy
    @0
    @25
    @19
    vx
    cA
    wsbc
    #
    @4
    wb
    @23
    @19
    wph
    vx
    cA
    cvv
    sbcbig
    @0
    @26
    @19
    @4
    @19
    vx
    cA
    cvv
    sbcg
    bibi1d
    bitrd
    albidv
    syl5bb
    @8
    @21
    vx
    cA
    wph
    vy
    @7
    abeq2
    sbcbii
    @4
    vy
    @7
    abeq2
    3bitr4g
    @9
    vx
    cA
    cvv
    vx
    vw
    cB
    sbcabel.1
    nfcri
    sbcgf
    anbi12d
    syl5bb
    exbidv
    syl5bb
    @2
    @11
    vx
    cA
    vw
    @1
    cB
    df-clel
    sbcbii
    vw
    @5
    cB
    df-clel
    3bitr4g
    syl
end
