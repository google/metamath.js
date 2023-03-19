include "cv.mm"
include "crn.mm"
include "wss.mm"
include "cuni.mm"
include "cima.mm"
include "cdif.mm"
include "wcel.mm"
include "wa.mm"
include "cab.mm"
include "sbthlem1.mm"
include "imass2.mm"
include "sscon.mm"
include "mp2b.mm"
include "wb.mm"
include "wi.mm"
include "imassrn.mm"
include "sstr2.mm"
include "ax-mp.mm"
include "difss.mm"
include "ssconb.mm"
include "sylancl.mm"
include "mpbiri.mm"
include "jctil.mm"
include "ssexi.mm"
include "wceq.mm"
include "sseq1.mm"
include "imaeq2.mm"
include "difeq2d.mm"
include "imaeq2d.mm"
include "difeq2.mm"
include "sseq12d.mm"
include "anbi12d.mm"
include "elab.mm"
include "sylibr.mm"
include "syl6eleqr.mm"
include "elssuni.mm"
include "syl.mm"

theorem sbthlem2
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cD: class D
  let vf: setvar f
  let vg: setvar g
  assume sbthlem.1: |- A e. _V
  assume sbthlem.2: |- D = { x | ( x C_ A /\ ( g " ( B \ ( f " x ) ) ) C_ ( A \ x ) ) }

  disjoint A x
  disjoint B x
  disjoint D x
  disjoint f x
  disjoint g x
  assert |- ( ran g C_ A -> ( A \ ( g " ( B \ ( f " U. D ) ) ) ) C_ U. D )

  proof
    vg
    cv
    #
    crn
    #
    cA
    wss
    #
    cA
    @0
    cB
    vf
    cv
    #
    cD
    cuni
    #
    cima
    #
    cdif
    #
    cima
    #
    cdif
    #
    cD
    wcel
    @8
    @4
    wss
    @2
    @8
    vx
    cv
    #
    cA
    wss
    #
    @0
    cB
    @3
    @9
    cima
    #
    cdif
    #
    cima
    #
    cA
    @9
    cdif
    #
    wss
    #
    wa
    #
    vx
    cab
    #
    cD
    @2
    @8
    cA
    wss
    #
    @0
    cB
    @3
    @8
    cima
    #
    cdif
    #
    cima
    #
    cA
    @8
    cdif
    #
    wss
    #
    wa
    #
    @8
    @17
    wcel
    @2
    @23
    @18
    @2
    @23
    @8
    cA
    @21
    cdif
    wss
    #
    @20
    @6
    wss
    #
    @21
    @7
    wss
    @25
    @4
    @8
    wss
    @5
    @19
    wss
    @26
    vx
    cA
    cB
    cD
    vf
    vg
    sbthlem.1
    sbthlem.2
    sbthlem1
    @4
    @8
    @3
    imass2
    @5
    @19
    cB
    sscon
    mp2b
    @20
    @6
    @0
    imass2
    @21
    @7
    cA
    sscon
    mp2b
    @2
    @21
    cA
    wss
    #
    @18
    @23
    @25
    wb
    @21
    @1
    wss
    @2
    @27
    wi
    @0
    @20
    imassrn
    @21
    @1
    cA
    sstr2
    ax-mp
    cA
    @7
    difss
    #
    @21
    @8
    cA
    ssconb
    sylancl
    mpbiri
    @28
    jctil
    @16
    @24
    vx
    @8
    @8
    cA
    sbthlem.1
    @28
    ssexi
    @9
    @8
    wceq
    #
    @10
    @18
    @15
    @23
    @9
    @8
    cA
    sseq1
    @29
    @13
    @21
    @14
    @22
    @29
    @12
    @20
    @0
    @29
    @11
    @19
    cB
    @9
    @8
    @3
    imaeq2
    difeq2d
    imaeq2d
    @9
    @8
    cA
    difeq2
    sseq12d
    anbi12d
    elab
    sylibr
    sbthlem.2
    syl6eleqr
    @8
    cD
    elssuni
    syl
end
