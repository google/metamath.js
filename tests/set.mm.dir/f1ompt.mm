include "wf.mm"
include "wf1o.mm"
include "wa.mm"
include "cv.mm"
include "wceq.mm"
include "wreu.mm"
include "wral.mm"
include "wcel.mm"
include "ccnv.mm"
include "wfn.mm"
include "wb.mm"
include "ffn.mm"
include "dff1o4.mm"
include "baib.mm"
include "syl.mm"
include "cres.mm"
include "wbr.mm"
include "weu.mm"
include "fnres.mm"
include "nfcv.mm"
include "cmpt.mm"
include "nfmpt1.mm"
include "nfcxfr.mm"
include "nfbr.mm"
include "nfv.mm"
include "breq1.mm"
include "copab.mm"
include "df-mpt.mm"
include "eqtri.mm"
include "breqi.mm"
include "cop.mm"
include "df-br.mm"
include "opabid.mm"
include "bitri.mm"
include "syl6bb.mm"
include "cbveu.mm"
include "vex.mm"
include "brcnv.mm"
include "eubii.mm"
include "df-reu.mm"
include "3bitr4i.mm"
include "ralbii.mm"
include "wrel.mm"
include "cdm.mm"
include "wss.mm"
include "relcnv.mm"
include "crn.mm"
include "df-rn.mm"
include "frn.mm"
include "syl5eqssr.mm"
include "relssres.mm"
include "sylancr.mm"
include "fneq1d.mm"
include "syl5bbr.mm"
include "bitr4d.mm"
include "pm5.32i.mm"
include "f1of.mm"
include "pm4.71ri.mm"
include "fmpt.mm"
include "anbi1i.mm"

theorem f1ompt
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F
  let vz: setvar z
  assume fmpt.1: |- F = ( x e. A |-> C )

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B x
  disjoint B y
  disjoint C y
  disjoint F y
  disjoint x z
  disjoint y z
  disjoint A z
  disjoint B z
  disjoint C z
  disjoint F z
  assert |- ( F : A -1-1-onto-> B <-> ( A. x e. A C e. B /\ A. y e. B E! x e. A y = C ) )

  proof
    cA
    cB
    cF
    wf
    #
    cA
    cB
    cF
    wf1o
    #
    wa
    @0
    vy
    cv
    #
    cC
    wceq
    #
    vx
    cA
    wreu
    #
    vy
    cB
    wral
    #
    wa
    @1
    cC
    cB
    wcel
    vx
    cA
    wral
    #
    @5
    wa
    @0
    @1
    @5
    @0
    @1
    cF
    ccnv
    #
    cB
    wfn
    #
    @5
    @0
    cF
    cA
    wfn
    #
    @1
    @8
    wb
    cA
    cB
    cF
    ffn
    @1
    @9
    @8
    cA
    cB
    cF
    dff1o4
    baib
    syl
    @5
    @7
    cB
    cres
    #
    cB
    wfn
    #
    @0
    @8
    @11
    @2
    vz
    cv
    #
    @7
    wbr
    #
    vz
    weu
    #
    vy
    cB
    wral
    @5
    vy
    vz
    cB
    @7
    fnres
    @14
    @4
    vy
    cB
    @12
    @2
    cF
    wbr
    #
    vz
    weu
    vx
    cv
    #
    cA
    wcel
    @3
    wa
    #
    vx
    weu
    @14
    @4
    @15
    @17
    vz
    vx
    vx
    @12
    @2
    cF
    vx
    @12
    nfcv
    vx
    cF
    vx
    cA
    cC
    cmpt
    #
    fmpt.1
    vx
    cA
    cC
    nfmpt1
    nfcxfr
    vx
    @2
    nfcv
    nfbr
    @17
    vz
    nfv
    @12
    @16
    wceq
    @15
    @16
    @2
    cF
    wbr
    #
    @17
    @12
    @16
    @2
    cF
    breq1
    @19
    @16
    @2
    @17
    vx
    vy
    copab
    #
    wbr
    #
    @17
    @16
    @2
    cF
    @20
    cF
    @18
    @20
    fmpt.1
    vx
    vy
    cA
    cC
    df-mpt
    eqtri
    breqi
    @21
    @16
    @2
    cop
    @20
    wcel
    @17
    @16
    @2
    @20
    df-br
    @17
    vx
    vy
    opabid
    bitri
    bitri
    syl6bb
    cbveu
    @13
    @15
    vz
    @2
    @12
    cF
    vy
    vex
    vz
    vex
    brcnv
    eubii
    @3
    vx
    cA
    df-reu
    3bitr4i
    ralbii
    bitri
    @0
    cB
    @10
    @7
    @0
    @7
    wrel
    @7
    cdm
    #
    cB
    wss
    @10
    @7
    wceq
    cF
    relcnv
    @0
    @22
    cF
    crn
    cB
    cF
    df-rn
    cA
    cB
    cF
    frn
    syl5eqssr
    @7
    cB
    relssres
    sylancr
    fneq1d
    syl5bbr
    bitr4d
    pm5.32i
    @1
    @0
    cA
    cB
    cF
    f1of
    pm4.71ri
    @6
    @0
    @5
    vx
    cA
    cB
    cC
    cF
    fmpt.1
    fmpt
    anbi1i
    3bitr4i
end
