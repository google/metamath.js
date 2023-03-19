include "ccom.mm"
include "cmpt.mm"
include "relco.mm"
include "mptrel.mm"
include "cv.mm"
include "wbr.mm"
include "wa.mm"
include "wex.mm"
include "wcel.mm"
include "csb.mm"
include "wceq.mm"
include "cop.mm"
include "cfv.mm"
include "wfun.mm"
include "fmpt3d.mm"
include "ffund.mm"
include "funbrfv.mm"
include "imp.mm"
include "sylan.mm"
include "eqcomd.mm"
include "a1d.mm"
include "expimpd.mm"
include "pm4.71rd.mm"
include "exbidv.mm"
include "fvex.mm"
include "breq2.mm"
include "breq1.mm"
include "anbi12d.mm"
include "ceqsexv.mm"
include "cdm.mm"
include "wb.mm"
include "funfvbrb.mm"
include "syl.mm"
include "wf.mm"
include "fdm.mm"
include "eleq2d.mm"
include "bitr3d.mm"
include "fveq1d.mm"
include "eqidd.mm"
include "breq123d.mm"
include "wi.mm"
include "nfcv.mm"
include "nfv.mm"
include "nffvmpt1.mm"
include "nfbr.mm"
include "nfcsb1v.mm"
include "nfeq2.mm"
include "nfbi.mm"
include "nfim.mm"
include "fveq2.mm"
include "breq1d.mm"
include "csbeq1a.mm"
include "eqeq2d.mm"
include "bibi12d.mm"
include "imbi2d.mm"
include "cvv.mm"
include "vex.mm"
include "simpl.mm"
include "eleq1d.mm"
include "id.mm"
include "eqeqan12rd.mm"
include "df-mpt.mm"
include "brabga.mm"
include "sylancl.mm"
include "eqid.mm"
include "fvmpt2.mm"
include "syl2an2.mm"
include "biantrurd.mm"
include "3bitr4d.mm"
include "expcom.mm"
include "vtoclgaf.mm"
include "impcom.mm"
include "pm5.32da.mm"
include "bitrd.mm"
include "syl5bb.mm"
include "opelco.mm"
include "copab.mm"
include "eleq2i.mm"
include "nfan.mm"
include "eleq1.mm"
include "eqeq1.mm"
include "anbi2d.mm"
include "opelopabf.mm"
include "bitri.mm"
include "3bitr4g.mm"
include "eqrelrdv.mm"

theorem fmptco
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cR: class R
  let cS: class S
  let cT: class T
  let cF: class F
  let cG: class G
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
  let vz: setvar z
  assume fmptco.1: |- ( ( ph /\ x e. A ) -> R e. B )
  assume fmptco.2: |- ( ph -> F = ( x e. A |-> R ) )
  assume fmptco.3: |- ( ph -> G = ( y e. B |-> S ) )
  assume fmptco.4: |- ( y = R -> S = T )

  disjoint A x
  disjoint x y
  disjoint B x
  disjoint B y
  disjoint R y
  disjoint ph x
  disjoint S x
  disjoint T y
  disjoint u v
  disjoint u w
  disjoint u x
  disjoint u z
  disjoint A u
  disjoint v w
  disjoint v x
  disjoint v z
  disjoint A v
  disjoint w x
  disjoint w z
  disjoint A w
  disjoint x z
  disjoint A z
  disjoint u y
  disjoint B u
  disjoint F u
  disjoint F w
  disjoint F z
  disjoint G u
  disjoint G w
  disjoint G z
  disjoint R u
  disjoint ph u
  disjoint ph w
  disjoint ph z
  disjoint S u
  disjoint T u
  disjoint v y
  disjoint T v
  disjoint w y
  disjoint T w
  disjoint y z
  disjoint T z
  assert |- ( ph -> ( G o. F ) = ( x e. A |-> T ) )

  proof
    wph
    vz
    vw
    cG
    cF
    ccom
    #
    vx
    cA
    cT
    cmpt
    #
    cG
    cF
    relco
    vx
    cA
    cT
    mptrel
    wph
    vz
    cv
    #
    vu
    cv
    #
    cF
    wbr
    #
    @3
    vw
    cv
    #
    cG
    wbr
    #
    wa
    #
    vu
    wex
    #
    @2
    cA
    wcel
    #
    @5
    vx
    @2
    cT
    csb
    #
    wceq
    #
    wa
    #
    @2
    @5
    cop
    #
    @0
    wcel
    @13
    @1
    wcel
    #
    wph
    @8
    @3
    @2
    cF
    cfv
    #
    wceq
    #
    @7
    wa
    #
    vu
    wex
    #
    @12
    wph
    @7
    @17
    vu
    wph
    @7
    @16
    wph
    @4
    @6
    @16
    wph
    @4
    wa
    #
    @16
    @6
    @19
    @15
    @3
    wph
    cF
    wfun
    #
    @4
    @15
    @3
    wceq
    #
    wph
    cA
    cB
    cF
    wph
    vx
    cA
    cR
    cB
    cF
    fmptco.2
    fmptco.1
    fmpt3d
    #
    ffund
    #
    @20
    @4
    @21
    @2
    @3
    cF
    funbrfv
    imp
    sylan
    eqcomd
    a1d
    expimpd
    pm4.71rd
    exbidv
    @18
    @2
    @15
    cF
    wbr
    #
    @15
    @5
    cG
    wbr
    #
    wa
    #
    wph
    @12
    @7
    @26
    vu
    @15
    @2
    cF
    fvex
    @16
    @4
    @24
    @6
    @25
    @3
    @15
    @2
    cF
    breq2
    @3
    @15
    @5
    cG
    breq1
    anbi12d
    ceqsexv
    wph
    @26
    @9
    @2
    vx
    cA
    cR
    cmpt
    #
    cfv
    #
    @5
    vy
    cB
    cS
    cmpt
    #
    wbr
    #
    wa
    @12
    wph
    @24
    @9
    @25
    @30
    wph
    @2
    cF
    cdm
    #
    wcel
    #
    @24
    @9
    wph
    @20
    @32
    @24
    wb
    @23
    @2
    cF
    funfvbrb
    syl
    wph
    @31
    cA
    @2
    wph
    cA
    cB
    cF
    wf
    @31
    cA
    wceq
    @22
    cA
    cB
    cF
    fdm
    syl
    eleq2d
    bitr3d
    wph
    @15
    @28
    @5
    @5
    cG
    @29
    wph
    @2
    cF
    @27
    fmptco.2
    fveq1d
    fmptco.3
    wph
    @5
    eqidd
    breq123d
    anbi12d
    wph
    @9
    @30
    @11
    @9
    wph
    @30
    @11
    wb
    #
    wph
    vx
    cv
    #
    @27
    cfv
    #
    @5
    @29
    wbr
    #
    @5
    cT
    wceq
    #
    wb
    #
    wi
    wph
    @33
    wi
    vx
    @2
    cA
    vx
    @2
    nfcv
    wph
    @33
    vx
    wph
    vx
    nfv
    @30
    @11
    vx
    vx
    @28
    @5
    @29
    vx
    cA
    cR
    @2
    nffvmpt1
    vx
    @29
    nfcv
    vx
    @5
    nfcv
    nfbr
    vx
    @5
    @10
    vx
    @2
    cT
    nfcsb1v
    #
    nfeq2
    nfbi
    nfim
    @34
    @2
    wceq
    #
    @38
    @33
    wph
    @40
    @36
    @30
    @37
    @11
    @40
    @35
    @28
    @5
    @29
    @34
    @2
    @27
    fveq2
    breq1d
    @40
    cT
    @10
    @5
    vx
    @2
    cT
    csbeq1a
    #
    eqeq2d
    bibi12d
    imbi2d
    wph
    @34
    cA
    wcel
    #
    @38
    wph
    @42
    wa
    #
    cR
    @5
    @29
    wbr
    #
    cR
    cB
    wcel
    #
    @37
    wa
    #
    @36
    @37
    @43
    @45
    @5
    cvv
    wcel
    @44
    @46
    wb
    fmptco.1
    vw
    vex
    #
    vy
    cv
    #
    cB
    wcel
    #
    @3
    cS
    wceq
    #
    wa
    @46
    vy
    vu
    cR
    @5
    @29
    cB
    cvv
    @48
    cR
    wceq
    #
    @3
    @5
    wceq
    #
    wa
    #
    @49
    @45
    @50
    @37
    @53
    @48
    cR
    cB
    @51
    @52
    simpl
    eleq1d
    @52
    @51
    @3
    @5
    cS
    cT
    @52
    id
    fmptco.4
    eqeqan12rd
    anbi12d
    vy
    vu
    cB
    cS
    df-mpt
    brabga
    sylancl
    @43
    @35
    cR
    @5
    @29
    @42
    @42
    wph
    @45
    @35
    cR
    wceq
    @42
    id
    fmptco.1
    vx
    cA
    cR
    cB
    @27
    @27
    eqid
    fvmpt2
    syl2an2
    breq1d
    @43
    @45
    @37
    fmptco.1
    biantrurd
    3bitr4d
    expcom
    vtoclgaf
    impcom
    pm5.32da
    bitrd
    syl5bb
    bitrd
    vu
    @2
    @5
    cG
    cF
    vz
    vex
    #
    @47
    opelco
    @14
    @13
    @42
    vv
    cv
    #
    cT
    wceq
    #
    wa
    #
    vx
    vv
    copab
    #
    wcel
    @12
    @1
    @58
    @13
    vx
    vv
    cA
    cT
    df-mpt
    eleq2i
    @57
    @9
    @55
    @10
    wceq
    #
    wa
    @12
    vx
    vv
    @2
    @5
    @9
    @59
    vx
    @9
    vx
    nfv
    vx
    @55
    @10
    @39
    nfeq2
    nfan
    @12
    vv
    nfv
    @54
    @47
    @40
    @42
    @9
    @56
    @59
    @34
    @2
    cA
    eleq1
    @40
    cT
    @10
    @55
    @41
    eqeq2d
    anbi12d
    @55
    @5
    wceq
    @59
    @11
    @9
    @55
    @5
    @10
    eqeq1
    anbi2d
    opelopabf
    bitri
    3bitr4g
    eqrelrdv
end
