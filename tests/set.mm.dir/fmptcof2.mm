include "ccom.mm"
include "cmpt.mm"
include "relco.mm"
include "wfun.mm"
include "wrel.mm"
include "funmpt.mm"
include "funrel.mm"
include "ax-mp.mm"
include "cv.mm"
include "wbr.mm"
include "wa.mm"
include "wex.mm"
include "wcel.mm"
include "csb.mm"
include "wceq.mm"
include "cop.mm"
include "cfv.mm"
include "wf.mm"
include "r19.21bi.mm"
include "eqid.mm"
include "fmptdF.mm"
include "feq1d.mm"
include "mpbird.mm"
include "ffun.mm"
include "syl.mm"
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
include "fdm.mm"
include "eleq2d.mm"
include "bitr3d.mm"
include "fveq1d.mm"
include "eqidd.mm"
include "breq123d.mm"
include "wi.mm"
include "nfcri.mm"
include "nffvmpt1.mm"
include "nfmpt.mm"
include "nfcv.mm"
include "nfbr.mm"
include "nfcsb1v.mm"
include "nfeq2.mm"
include "nfbi.mm"
include "nfim.mm"
include "eleq1.mm"
include "fveq2.mm"
include "breq1d.mm"
include "csbeq1a.mm"
include "eqeq2d.mm"
include "bibi12d.mm"
include "imbi2d.mm"
include "imbi12d.mm"
include "cvv.mm"
include "vex.mm"
include "nfv.mm"
include "nfeq.mm"
include "nfan.mm"
include "simpl.mm"
include "eleq1d.mm"
include "simpr.mm"
include "adantr.mm"
include "eqeq12d.mm"
include "df-mpt.mm"
include "brabgaf.mm"
include "sylancl.mm"
include "fvmpt2f.mm"
include "syl2anc.mm"
include "biantrurd.mm"
include "3bitr4d.mm"
include "expcom.mm"
include "chvar.mm"
include "impcom.mm"
include "pm5.32da.mm"
include "bitrd.mm"
include "syl5bb.mm"
include "opelco.mm"
include "copab.mm"
include "eleq2i.mm"
include "eqeq1.mm"
include "anbi2d.mm"
include "opelopabf.mm"
include "bitri.mm"
include "3bitr4g.mm"
include "eqrelrdv.mm"

theorem fmptcof2
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
  assume fmptcof2.x: |- F/_ x S
  assume fmptcof2.y: |- F/_ y T
  assume fmptcof2.1: |- F/_ x A
  assume fmptcof2.2: |- F/_ x B
  assume fmptcof2.3: |- F/ x ph
  assume fmptcof2.4: |- ( ph -> A. x e. A R e. B )
  assume fmptcof2.5: |- ( ph -> F = ( x e. A |-> R ) )
  assume fmptcof2.6: |- ( ph -> G = ( y e. B |-> S ) )
  assume fmptcof2.7: |- ( y = R -> S = T )

  disjoint x y
  disjoint B y
  disjoint R y
  disjoint u v
  disjoint u w
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint v w
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint x z
  disjoint y z
  disjoint A u
  disjoint A v
  disjoint A w
  disjoint A z
  disjoint B u
  disjoint F u
  disjoint F w
  disjoint F z
  disjoint G u
  disjoint G w
  disjoint G z
  disjoint R u
  disjoint S u
  disjoint T u
  disjoint T v
  disjoint T w
  disjoint T z
  disjoint ph u
  disjoint ph w
  disjoint ph z
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
    @1
    wfun
    @1
    wrel
    vx
    cA
    cT
    funmpt
    @1
    funrel
    ax-mp
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
    wf
    #
    @20
    wph
    @22
    cA
    cB
    vx
    cA
    cR
    cmpt
    #
    wf
    wph
    vx
    cA
    cR
    cB
    @23
    fmptcof2.3
    fmptcof2.1
    fmptcof2.2
    wph
    cR
    cB
    wcel
    #
    vx
    cA
    fmptcof2.4
    r19.21bi
    #
    @23
    eqid
    fmptdF
    wph
    cA
    cB
    cF
    @23
    fmptcof2.5
    feq1d
    mpbird
    #
    cA
    cB
    cF
    ffun
    syl
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
    @30
    vu
    @15
    @2
    cF
    fvex
    @16
    @4
    @28
    @6
    @29
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
    @30
    @9
    @2
    @23
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
    @28
    @9
    @29
    @33
    wph
    @2
    cF
    cdm
    #
    wcel
    #
    @28
    @9
    wph
    @20
    @35
    @28
    wb
    @27
    @2
    cF
    funfvbrb
    syl
    wph
    @34
    cA
    @2
    wph
    @22
    @34
    cA
    wceq
    @26
    cA
    cB
    cF
    fdm
    syl
    eleq2d
    bitr3d
    wph
    @15
    @31
    @5
    @5
    cG
    @32
    wph
    @2
    cF
    @23
    fmptcof2.5
    fveq1d
    fmptcof2.6
    wph
    @5
    eqidd
    breq123d
    anbi12d
    wph
    @9
    @33
    @11
    @9
    wph
    @33
    @11
    wb
    #
    vx
    cv
    #
    cA
    wcel
    #
    wph
    @37
    @23
    cfv
    #
    @5
    @32
    wbr
    #
    @5
    cT
    wceq
    #
    wb
    #
    wi
    #
    wi
    @9
    wph
    @36
    wi
    #
    wi
    vx
    vz
    @9
    @44
    vx
    vx
    vz
    cA
    fmptcof2.1
    nfcri
    #
    wph
    @36
    vx
    fmptcof2.3
    @33
    @11
    vx
    vx
    @31
    @5
    @32
    vx
    cA
    cR
    @2
    nffvmpt1
    vx
    vy
    cB
    cS
    fmptcof2.2
    fmptcof2.x
    nfmpt
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
    nfim
    @37
    @2
    wceq
    #
    @38
    @9
    @43
    @44
    @37
    @2
    cA
    eleq1
    #
    @47
    @42
    @36
    wph
    @47
    @40
    @33
    @41
    @11
    @47
    @39
    @31
    @5
    @32
    @37
    @2
    @23
    fveq2
    breq1d
    @47
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
    imbi12d
    wph
    @38
    @42
    wph
    @38
    wa
    #
    cR
    @5
    @32
    wbr
    #
    @24
    @41
    wa
    #
    @40
    @41
    @50
    @24
    @5
    cvv
    wcel
    @51
    @52
    wb
    @25
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
    @52
    vy
    vu
    cR
    @5
    @32
    cB
    cvv
    @24
    @41
    vy
    @24
    vy
    nfv
    vy
    @5
    cT
    vy
    @5
    nfcv
    fmptcof2.y
    nfeq
    nfan
    @54
    cR
    wceq
    #
    @3
    @5
    wceq
    #
    wa
    #
    @55
    @24
    @56
    @41
    @59
    @54
    cR
    cB
    @57
    @58
    simpl
    eleq1d
    @59
    @3
    @5
    cS
    cT
    @57
    @58
    simpr
    @57
    cS
    cT
    wceq
    @58
    fmptcof2.7
    adantr
    eqeq12d
    anbi12d
    vy
    vu
    cB
    cS
    df-mpt
    brabgaf
    sylancl
    @50
    @39
    cR
    @5
    @32
    @50
    @38
    @24
    @39
    cR
    wceq
    wph
    @38
    simpr
    @25
    vx
    cA
    cR
    cB
    fmptcof2.1
    fvmpt2f
    syl2anc
    breq1d
    @50
    @24
    @41
    @25
    biantrurd
    3bitr4d
    expcom
    chvar
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
    @53
    opelco
    @14
    @13
    @38
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
    @64
    @13
    vx
    vv
    cA
    cT
    df-mpt
    eleq2i
    @63
    @9
    @61
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
    @65
    vx
    @45
    vx
    @61
    @10
    @46
    nfeq2
    nfan
    @12
    vv
    nfv
    @60
    @53
    @47
    @38
    @9
    @62
    @65
    @48
    @47
    cT
    @10
    @61
    @49
    eqeq2d
    anbi12d
    @61
    @5
    wceq
    @65
    @11
    @9
    @61
    @5
    @10
    eqeq1
    anbi2d
    opelopabf
    bitri
    3bitr4g
    eqrelrdv
end
