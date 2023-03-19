include "cres.mm"
include "cima.mm"
include "cuni.mm"
include "cfv.mm"
include "cv.mm"
include "csn.mm"
include "co.mm"
include "cmpt.mm"
include "cdprd.mm"
include "crn.mm"
include "csubg.mm"
include "cbs.mm"
include "cgrp.mm"
include "wcel.mm"
include "cacs.mm"
include "cmre.mm"
include "cdm.mm"
include "wbr.mm"
include "dprdgrp.mm"
include "syl.mm"
include "eqid.mm"
include "subgacs.mm"
include "acsmre.mm"
include "3syl.mm"
include "ciun.mm"
include "wf.mm"
include "wfun.mm"
include "wceq.mm"
include "ffun.mm"
include "funiunfv.mm"
include "wss.mm"
include "wral.mm"
include "wa.mm"
include "c1st.mm"
include "resss.mm"
include "sseli.mm"
include "dprd2dlem2.mm"
include "sylan2.mm"
include "cvv.mm"
include "c2nd.mm"
include "cop.mm"
include "wrel.mm"
include "1st2nd.mm"
include "syl2an.mm"
include "simpr.mm"
include "eqeltrrd.mm"
include "fvex.mm"
include "opelres.mm"
include "simprbi.mm"
include "ovex.mm"
include "sneq.mm"
include "imaeq2d.mm"
include "oveq1.mm"
include "mpteq12dv.mm"
include "oveq2d.mm"
include "elrnmpt1s.mm"
include "sylancl.mm"
include "elssuni.mm"
include "sstrd.mm"
include "ralrimiva.mm"
include "iunss.mm"
include "sylibr.mm"
include "eqsstr3d.mm"
include "cpw.mm"
include "sselda.mm"
include "syldan.mm"
include "dmmpti.mm"
include "a1i.mm"
include "imassrn.mm"
include "frn.mm"
include "mresspw.mm"
include "syl5ss.mm"
include "sspwuni.mm"
include "sylib.mm"
include "mrccl.mm"
include "syl2anc.mm"
include "adantr.mm"
include "oveq2.mm"
include "fvmpt3i.mm"
include "adantl.mm"
include "df-ov.mm"
include "wfn.mm"
include "ffn.mm"
include "ad2antrr.mm"
include "wb.mm"
include "elrelimasn.mm"
include "biimpa.mm"
include "df-br.mm"
include "simplr.mm"
include "vex.mm"
include "sylanbrc.mm"
include "fnfvima.mm"
include "syl3anc.mm"
include "syl5eqel.mm"
include "mrcssidd.mm"
include "eqsstrd.mm"
include "dprdlub.mm"
include "elpw.mm"
include "fmptd.mm"
include "mrcssvd.mm"
include "mrcssd.mm"
include "mrcsscl.mm"
include "eqssd.mm"
include "dprdres.mm"
include "simpld.mm"
include "resmptd.mm"
include "breqtrd.mm"
include "dprdspan.mm"
include "eqtr4d.mm"

theorem dprd2dlem1
  let wph: wff ph
  let cA: class A
  let cC: class C
  let cS: class S
  let vi: setvar i
  let vj: setvar j
  let cG: class G
  let cI: class I
  let cK: class K
  let vk: setvar k
  let vx: setvar x
  let vy: setvar y
  let cX: class X
  assume dprd2d.1: |- ( ph -> Rel A )
  assume dprd2d.2: |- ( ph -> S : A --> ( SubGrp ` G ) )
  assume dprd2d.3: |- ( ph -> dom A C_ I )
  assume dprd2d.4: |- ( ( ph /\ i e. I ) -> G dom DProd ( j e. ( A " { i } ) |-> ( i S j ) ) )
  assume dprd2d.5: |- ( ph -> G dom DProd ( i e. I |-> ( G DProd ( j e. ( A " { i } ) |-> ( i S j ) ) ) ) )
  assume dprd2d.k: |- K = ( mrCls ` ( SubGrp ` G ) )
  assume dprd2d.6: |- ( ph -> C C_ I )

  disjoint i j
  disjoint A i
  disjoint A j
  disjoint C i
  disjoint G i
  disjoint G j
  disjoint I i
  disjoint K i
  disjoint i ph
  disjoint j ph
  disjoint S i
  disjoint S j
  disjoint i k
  disjoint i x
  disjoint i y
  disjoint j k
  disjoint j x
  disjoint j y
  disjoint k x
  disjoint k y
  disjoint A k
  disjoint x y
  disjoint A x
  disjoint A y
  disjoint C k
  disjoint C x
  disjoint G k
  disjoint G x
  disjoint G y
  disjoint K k
  disjoint k ph
  disjoint ph x
  disjoint ph y
  disjoint S k
  disjoint S x
  disjoint S y
  disjoint X i
  disjoint X j
  assert |- ( ph -> ( K ` U. ( S " ( A |` C ) ) ) = ( G DProd ( i e. C |-> ( G DProd ( j e. ( A " { i } ) |-> ( i S j ) ) ) ) ) )

  proof
    wph
    cS
    cA
    cC
    cres
    #
    cima
    #
    cuni
    #
    cK
    cfv
    #
    vi
    cC
    cG
    vj
    cA
    vi
    cv
    #
    csn
    #
    cima
    #
    @4
    vj
    cv
    #
    cS
    co
    #
    cmpt
    #
    cdprd
    co
    #
    cmpt
    #
    crn
    #
    cuni
    #
    cK
    cfv
    #
    cG
    @11
    cdprd
    co
    #
    wph
    @3
    @14
    wph
    cG
    csubg
    cfv
    #
    @2
    cK
    @13
    cG
    cbs
    cfv
    #
    wph
    cG
    cgrp
    wcel
    #
    @16
    @17
    cacs
    cfv
    wcel
    @16
    @17
    cmre
    cfv
    wcel
    #
    wph
    cG
    vi
    cI
    @10
    cmpt
    #
    cdprd
    cdm
    #
    wbr
    @18
    dprd2d.5
    @20
    cG
    dprdgrp
    syl
    @17
    cG
    @17
    eqid
    subgacs
    @16
    @17
    acsmre
    3syl
    #
    dprd2d.k
    wph
    @2
    vx
    @0
    vx
    cv
    #
    cS
    cfv
    #
    ciun
    #
    @13
    wph
    cA
    @16
    cS
    wf
    #
    cS
    wfun
    @25
    @2
    wceq
    dprd2d.2
    cA
    @16
    cS
    ffun
    vx
    @0
    cS
    funiunfv
    3syl
    wph
    @24
    @13
    wss
    #
    vx
    @0
    wral
    @25
    @13
    wss
    wph
    @27
    vx
    @0
    wph
    @23
    @0
    wcel
    #
    wa
    #
    @24
    cG
    vj
    cA
    @23
    c1st
    cfv
    #
    csn
    #
    cima
    #
    @30
    @7
    cS
    co
    #
    cmpt
    #
    cdprd
    co
    #
    @13
    @28
    wph
    @23
    cA
    wcel
    #
    @24
    @35
    wss
    @0
    cA
    @23
    cA
    cC
    resss
    #
    sseli
    #
    wph
    cA
    cS
    vi
    vj
    cG
    cI
    cK
    @23
    dprd2d.1
    dprd2d.2
    dprd2d.3
    dprd2d.4
    dprd2d.5
    dprd2d.k
    dprd2dlem2
    sylan2
    @29
    @35
    @12
    wcel
    #
    @35
    @13
    wss
    @29
    @30
    cC
    wcel
    #
    @35
    cvv
    wcel
    @39
    @29
    @30
    @23
    c2nd
    cfv
    #
    cop
    #
    @0
    wcel
    #
    @40
    @29
    @23
    @42
    @0
    wph
    cA
    wrel
    #
    @36
    @23
    @42
    wceq
    @28
    dprd2d.1
    @38
    @23
    cA
    1st2nd
    syl2an
    wph
    @28
    simpr
    eqeltrrd
    @43
    @42
    cA
    wcel
    @40
    @30
    @41
    cA
    cC
    @23
    c2nd
    fvex
    opelres
    simprbi
    syl
    cG
    @34
    cdprd
    ovex
    vi
    cC
    @10
    @35
    @30
    @11
    cvv
    @11
    eqid
    #
    @4
    @30
    wceq
    #
    @9
    @34
    cG
    cdprd
    @46
    vj
    @6
    @8
    @32
    @33
    @46
    @5
    @31
    cA
    @4
    @30
    sneq
    imaeq2d
    @4
    @30
    @7
    cS
    oveq1
    mpteq12dv
    oveq2d
    elrnmpt1s
    sylancl
    @35
    @12
    elssuni
    syl
    sstrd
    ralrimiva
    vx
    @0
    @24
    @13
    iunss
    sylibr
    eqsstr3d
    wph
    @13
    @3
    @17
    wph
    @12
    @3
    cpw
    #
    wss
    #
    @13
    @3
    wss
    #
    wph
    cC
    @47
    @11
    wf
    @48
    wph
    vi
    cC
    @10
    @47
    @11
    wph
    @4
    cC
    wcel
    #
    wa
    #
    @10
    @3
    wss
    @10
    @47
    wcel
    @51
    @9
    @3
    vk
    cG
    @6
    wph
    @50
    @4
    cI
    wcel
    cG
    @9
    @21
    wbr
    wph
    cC
    cI
    @4
    dprd2d.6
    sselda
    dprd2d.4
    syldan
    @9
    cdm
    @6
    wceq
    @51
    vj
    @6
    @8
    @9
    @4
    @7
    cS
    ovex
    #
    @9
    eqid
    #
    dmmpti
    a1i
    wph
    @3
    @16
    wcel
    #
    @50
    wph
    @19
    @2
    @17
    wss
    #
    @54
    @22
    wph
    @1
    @17
    cpw
    #
    wss
    @55
    wph
    @1
    cS
    crn
    #
    @56
    cS
    @0
    imassrn
    wph
    @57
    @16
    @56
    wph
    @26
    @57
    @16
    wss
    dprd2d.2
    cA
    @16
    cS
    frn
    syl
    wph
    @19
    @16
    @56
    wss
    @22
    @16
    @17
    mresspw
    syl
    sstrd
    syl5ss
    @1
    @17
    sspwuni
    sylib
    #
    @16
    @2
    cK
    @17
    dprd2d.k
    mrccl
    syl2anc
    #
    adantr
    @51
    vk
    cv
    #
    @6
    wcel
    #
    wa
    #
    @60
    @9
    cfv
    #
    @4
    @60
    cS
    co
    #
    @3
    @61
    @63
    @64
    wceq
    @51
    vj
    @60
    @8
    @64
    @6
    @9
    @7
    @60
    @4
    cS
    oveq2
    @53
    @52
    fvmpt3i
    adantl
    @62
    @64
    @2
    @3
    @62
    @64
    @1
    wcel
    @64
    @2
    wss
    @62
    @64
    @4
    @60
    cop
    #
    cS
    cfv
    #
    @1
    @4
    @60
    cS
    df-ov
    @62
    cS
    cA
    wfn
    #
    @0
    cA
    wss
    #
    @65
    @0
    wcel
    #
    @66
    @1
    wcel
    wph
    @67
    @50
    @61
    wph
    @26
    @67
    dprd2d.2
    cA
    @16
    cS
    ffn
    syl
    ad2antrr
    @68
    @62
    @37
    a1i
    @62
    @65
    cA
    wcel
    #
    @50
    @69
    @62
    @4
    @60
    cA
    wbr
    #
    @70
    @51
    @61
    @71
    wph
    @61
    @71
    wb
    #
    @50
    wph
    @44
    @72
    dprd2d.1
    @4
    @60
    cA
    elrelimasn
    syl
    adantr
    biimpa
    @4
    @60
    cA
    df-br
    sylib
    wph
    @50
    @61
    simplr
    @4
    @60
    cA
    cC
    vk
    vex
    opelres
    sylanbrc
    cA
    @0
    cS
    @65
    fnfvima
    syl3anc
    syl5eqel
    @64
    @1
    elssuni
    syl
    wph
    @2
    @3
    wss
    @50
    @61
    wph
    @16
    @2
    cK
    @17
    @22
    dprd2d.k
    @58
    mrcssidd
    ad2antrr
    sstrd
    eqsstrd
    dprdlub
    @10
    @3
    cG
    @9
    cdprd
    ovex
    #
    elpw
    sylibr
    @45
    fmptd
    cC
    @47
    @11
    frn
    syl
    @12
    @3
    sspwuni
    sylib
    #
    wph
    @16
    @2
    cK
    @17
    @22
    dprd2d.k
    mrcssvd
    sstrd
    mrcssd
    wph
    @19
    @49
    @54
    @14
    @3
    wss
    @22
    @74
    @59
    @16
    @13
    cK
    @3
    @17
    dprd2d.k
    mrcsscl
    syl3anc
    eqssd
    wph
    cG
    @11
    @21
    wbr
    @15
    @14
    wceq
    wph
    cG
    @20
    cC
    cres
    #
    @11
    @21
    wph
    cG
    @75
    @21
    wbr
    cG
    @75
    cdprd
    co
    cG
    @20
    cdprd
    co
    wss
    wph
    cC
    @20
    cG
    cI
    dprd2d.5
    @20
    cdm
    cI
    wceq
    wph
    vi
    cI
    @10
    @20
    @73
    @20
    eqid
    dmmpti
    a1i
    dprd2d.6
    dprdres
    simpld
    wph
    vi
    cI
    cC
    @10
    dprd2d.6
    resmptd
    breqtrd
    @11
    cG
    cK
    dprd2d.k
    dprdspan
    syl
    eqtr4d
end
