include "wcel.mm"
include "cpw.mm"
include "wf1o.mm"
include "cv.mm"
include "crpss.mm"
include "wbr.mm"
include "cfv.mm"
include "ccnv.mm"
include "wb.mm"
include "wral.mm"
include "wiso.mm"
include "wfn.mm"
include "cdif.mm"
include "cvv.mm"
include "difexg.mm"
include "ralrimivw.mm"
include "fnmpt.mm"
include "syl.mm"
include "compsscnv.mm"
include "fneq1i.mm"
include "sylibr.mm"
include "dff1o4.mm"
include "sylanbrc.mm"
include "wa.mm"
include "wpss.mm"
include "wss.mm"
include "wceq.mm"
include "elpwi.mm"
include "ad2antll.mm"
include "isf34lem1.mm"
include "syldan.mm"
include "ad2antrl.mm"
include "psseq12d.mm"
include "difss.mm"
include "pssdifcom1.mm"
include "sylancl.mm"
include "dfss4.mm"
include "sylib.mm"
include "psseq1d.mm"
include "3bitrrd.mm"
include "vex.mm"
include "brrpss.mm"
include "fvex.mm"
include "3bitr4g.mm"
include "relrpss.mm"
include "relbrcnv.mm"
include "syl6bbr.mm"
include "ralrimivva.mm"
include "df-isom.mm"

theorem compssiso
  let vx: setvar x
  let cA: class A
  let cF: class F
  let cV: class V
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vf: setvar f
  let vg: setvar g
  let vy: setvar y
  let cX: class X
  let cG: class G
  assume compss.a: |- F = ( x e. ~P A |-> ( A \ x ) )

  disjoint A x
  disjoint V x
  disjoint a b
  disjoint a c
  disjoint a f
  disjoint a g
  disjoint a x
  disjoint a y
  disjoint A a
  disjoint b c
  disjoint b f
  disjoint b g
  disjoint b x
  disjoint b y
  disjoint A b
  disjoint c f
  disjoint c g
  disjoint c x
  disjoint c y
  disjoint A c
  disjoint f g
  disjoint f x
  disjoint f y
  disjoint A f
  disjoint g x
  disjoint g y
  disjoint A g
  disjoint x y
  disjoint A y
  disjoint F a
  disjoint F b
  disjoint F f
  disjoint F y
  disjoint V a
  disjoint V b
  disjoint V c
  disjoint V y
  disjoint X a
  disjoint X b
  disjoint X c
  disjoint G y
  assert |- ( A e. V -> F Isom [C.] , `' [C.] ( ~P A , ~P A ) )

  proof
    cA
    cV
    wcel
    #
    cA
    cpw
    #
    @1
    cF
    wf1o
    #
    va
    cv
    #
    vb
    cv
    #
    crpss
    wbr
    #
    @3
    cF
    cfv
    #
    @4
    cF
    cfv
    #
    crpss
    ccnv
    #
    wbr
    #
    wb
    #
    vb
    @1
    wral
    va
    @1
    wral
    @1
    @1
    crpss
    @8
    cF
    wiso
    @0
    cF
    @1
    wfn
    #
    cF
    ccnv
    #
    @1
    wfn
    #
    @2
    @0
    cA
    vx
    cv
    #
    cdif
    #
    cvv
    wcel
    #
    vx
    @1
    wral
    @11
    @0
    @16
    vx
    @1
    cA
    @14
    cV
    difexg
    ralrimivw
    vx
    @1
    @15
    cF
    cvv
    compss.a
    fnmpt
    syl
    #
    @0
    @11
    @13
    @17
    @1
    @12
    cF
    vx
    cA
    cF
    compss.a
    compsscnv
    fneq1i
    sylibr
    @1
    @1
    cF
    dff1o4
    sylanbrc
    @0
    @10
    va
    vb
    @1
    @1
    @0
    @3
    @1
    wcel
    #
    @4
    @1
    wcel
    #
    wa
    #
    wa
    #
    @5
    @7
    @6
    crpss
    wbr
    #
    @9
    @21
    @3
    @4
    wpss
    #
    @7
    @6
    wpss
    #
    @5
    @22
    @21
    @24
    cA
    @4
    cdif
    #
    cA
    @3
    cdif
    #
    wpss
    #
    cA
    @26
    cdif
    #
    @4
    wpss
    #
    @23
    @21
    @7
    @25
    @6
    @26
    @0
    @20
    @4
    cA
    wss
    #
    @7
    @25
    wceq
    @19
    @30
    @0
    @18
    @4
    cA
    elpwi
    ad2antll
    #
    vx
    cA
    cF
    cV
    @4
    compss.a
    isf34lem1
    syldan
    @0
    @20
    @3
    cA
    wss
    #
    @6
    @26
    wceq
    @18
    @32
    @0
    @19
    @3
    cA
    elpwi
    ad2antrl
    #
    vx
    cA
    cF
    cV
    @3
    compss.a
    isf34lem1
    syldan
    psseq12d
    @21
    @30
    @26
    cA
    wss
    @27
    @29
    wb
    @31
    cA
    @3
    difss
    @4
    @26
    cA
    pssdifcom1
    sylancl
    @21
    @28
    @3
    @4
    @21
    @32
    @28
    @3
    wceq
    @33
    @3
    cA
    dfss4
    sylib
    psseq1d
    3bitrrd
    @3
    @4
    vb
    vex
    brrpss
    @7
    @6
    @3
    cF
    fvex
    brrpss
    3bitr4g
    @6
    @7
    crpss
    relrpss
    relbrcnv
    syl6bbr
    ralrimivva
    va
    vb
    @1
    @1
    crpss
    @8
    cF
    df-isom
    sylanbrc
end
