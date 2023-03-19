include "cuni.mm"
include "wfun.mm"
include "cv.mm"
include "cres.mm"
include "wceq.mm"
include "wral.mm"
include "wa.mm"
include "wcel.mm"
include "wi.mm"
include "wal.mm"
include "nfv.mm"
include "nfcii.mm"
include "nfcri.mm"
include "nfim.mm"
include "eleq1.mm"
include "funeq.mm"
include "imbi12d.mm"
include "cbval.mm"
include "df-ral.mm"
include "3bitr4i.mm"
include "nfral.mm"
include "cdm.mm"
include "cin.mm"
include "dmeq.mm"
include "ineq1d.mm"
include "3eqtr4g.mm"
include "reseq2d.mm"
include "reseq1.mm"
include "eqtrd.mm"
include "eqeq12d.mm"
include "ralbidv.mm"
include "anbi12i.mm"
include "bnj1383.mm"
include "sylbi.mm"

theorem bnj1385
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cA: class A
  let cD: class D
  let vf: setvar f
  let vg: setvar g
  let vh: setvar h
  let cE: class E
  let bnjwphm: wff ph'
  let bnjwpsm: wff ps'
  assume bnj1385.1: |- ( ph <-> A. f e. A Fun f )
  assume bnj1385.2: |- D = ( dom f i^i dom g )
  assume bnj1385.3: |- ( ps <-> ( ph /\ A. f e. A A. g e. A ( f |` D ) = ( g |` D ) ) )
  assume bnj1385.4: |- ( x e. A -> A. f x e. A )
  assume bnj1385.5: |- ( ph' <-> A. h e. A Fun h )
  assume bnj1385.6: |- E = ( dom h i^i dom g )
  assume bnj1385.7: |- ( ps' <-> ( ph' /\ A. h e. A A. g e. A ( h |` E ) = ( g |` E ) ) )

  disjoint A g
  disjoint A h
  disjoint A x
  disjoint g h
  disjoint g x
  disjoint h x
  disjoint D h
  disjoint E f
  disjoint f g
  disjoint f h
  disjoint f x
  disjoint g ph'
  assert |- ( ps -> Fun U. A )

  proof
    wps
    bnjwpsm
    cA
    cuni
    wfun
    wph
    vf
    cv
    #
    cD
    cres
    #
    vg
    cv
    #
    cD
    cres
    #
    wceq
    #
    vg
    cA
    wral
    #
    vf
    cA
    wral
    #
    wa
    bnjwphm
    vh
    cv
    #
    cE
    cres
    #
    @2
    cE
    cres
    #
    wceq
    #
    vg
    cA
    wral
    #
    vh
    cA
    wral
    #
    wa
    wps
    bnjwpsm
    wph
    bnjwphm
    @6
    @12
    @0
    wfun
    #
    vf
    cA
    wral
    #
    @7
    wfun
    #
    vh
    cA
    wral
    #
    wph
    bnjwphm
    @0
    cA
    wcel
    #
    @13
    wi
    #
    vf
    wal
    @7
    cA
    wcel
    #
    @15
    wi
    #
    vh
    wal
    @14
    @16
    @18
    @20
    vf
    vh
    @18
    vh
    nfv
    @19
    @15
    vf
    vf
    vh
    cA
    vf
    vx
    cA
    bnj1385.4
    nfcii
    #
    nfcri
    #
    @15
    vf
    nfv
    nfim
    @0
    @7
    wceq
    #
    @17
    @19
    @13
    @15
    @0
    @7
    cA
    eleq1
    #
    @0
    @7
    funeq
    imbi12d
    cbval
    @13
    vf
    cA
    df-ral
    @15
    vh
    cA
    df-ral
    3bitr4i
    bnj1385.1
    bnj1385.5
    3bitr4i
    @17
    @5
    wi
    #
    vf
    wal
    @19
    @11
    wi
    #
    vh
    wal
    @6
    @12
    @25
    @26
    vf
    vh
    @25
    vh
    nfv
    @19
    @11
    vf
    @22
    @10
    vf
    vg
    cA
    @21
    @10
    vf
    nfv
    nfral
    nfim
    @23
    @17
    @19
    @5
    @11
    @24
    @23
    @4
    @10
    vg
    cA
    @23
    @1
    @8
    @3
    @9
    @23
    @1
    @0
    cE
    cres
    @8
    @23
    cD
    cE
    @0
    @23
    @0
    cdm
    #
    @2
    cdm
    #
    cin
    @7
    cdm
    #
    @28
    cin
    cD
    cE
    @23
    @27
    @29
    @28
    @0
    @7
    dmeq
    ineq1d
    bnj1385.2
    bnj1385.6
    3eqtr4g
    #
    reseq2d
    @0
    @7
    cE
    reseq1
    eqtrd
    @23
    cD
    cE
    @2
    @30
    reseq2d
    eqeq12d
    ralbidv
    imbi12d
    cbval
    @5
    vf
    cA
    df-ral
    @11
    vh
    cA
    df-ral
    3bitr4i
    anbi12i
    bnj1385.3
    bnj1385.7
    3bitr4i
    bnjwphm
    bnjwpsm
    cA
    cE
    vh
    vg
    bnj1385.5
    bnj1385.6
    bnj1385.7
    bnj1383
    sylbi
end
