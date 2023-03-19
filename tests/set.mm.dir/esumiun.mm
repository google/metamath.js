include "ciun.mm"
include "cv.mm"
include "crn.mm"
include "wf1o.mm"
include "cfv.mm"
include "c2nd.mm"
include "wceq.mm"
include "wral.mm"
include "wa.mm"
include "csn.mm"
include "cxp.mm"
include "wss.mm"
include "cesum.mm"
include "cle.mm"
include "wbr.mm"
include "wf1.mm"
include "wex.mm"
include "aciunf1.mm"
include "f1f1orn.mm"
include "anim1i.mm"
include "wf.mm"
include "f1f.mm"
include "frn.mm"
include "syl.mm"
include "adantr.mm"
include "jca.mm"
include "eximi.mm"
include "csb.mm"
include "ccnv.mm"
include "cvv.mm"
include "nfv.mm"
include "nfcv.mm"
include "nfcsb1v.mm"
include "csbeq1a.mm"
include "wcel.mm"
include "ralrimiva.mm"
include "iunexg.mm"
include "syl2anc.mm"
include "simprl.mm"
include "f1ocnv.mm"
include "adantrlr.mm"
include "nfiu1.mm"
include "nfrn.mm"
include "nff1o.mm"
include "nfral.mm"
include "nfan.mm"
include "nfss.mm"
include "simpr.mm"
include "fveq2d.mm"
include "simplr.mm"
include "simp-4r.mm"
include "simpld.mm"
include "simprd.mm"
include "ad2antrr.mm"
include "fveq2.mm"
include "id.mm"
include "eqeq12d.mm"
include "rspcva.mm"
include "eqtr3d.mm"
include "f1ocnvfv1.mm"
include "3eqtr2rd.mm"
include "wfn.mm"
include "wrex.mm"
include "f1ofn.mm"
include "simpllr.mm"
include "fvelrnb.mm"
include "biimpa.mm"
include "r19.29a.mm"
include "simprr.mm"
include "sselda.mm"
include "eliun.mm"
include "sylib.mm"
include "r19.29af.mm"
include "cc0.mm"
include "cpnf.mm"
include "cicc.mm"
include "co.mm"
include "nfel.mm"
include "adantllr.mm"
include "biimpi.mm"
include "adantl.mm"
include "adantlr.mm"
include "esumf1o.mm"
include "eqcomd.mm"
include "snex.mm"
include "a1i.mm"
include "xpexg.mm"
include "c1st.mm"
include "nfcsb.mm"
include "simplll.mm"
include "rspcsbela.mm"
include "xp1st.mm"
include "elsni.mm"
include "xp2nd.mm"
include "reximi.mm"
include "sylbi.mm"
include "r19.29af2.mm"
include "esummono.mm"
include "eqbrtrrd.mm"
include "cop.mm"
include "vex.mm"
include "op2ndd.mm"
include "anasss.mm"
include "esum2d.mm"
include "breqtrrd.mm"
include "exlimddv.mm"

theorem esumiun
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let vj: setvar j
  let vk: setvar k
  let cV: class V
  let cW: class W
  let vf: setvar f
  let vl: setvar l
  let vz: setvar z
  assume esumiun.0: |- ( ph -> A e. V )
  assume esumiun.1: |- ( ( ph /\ j e. A ) -> B e. W )
  assume esumiun.2: |- ( ( ( ph /\ j e. A ) /\ k e. B ) -> C e. ( 0 [,] +oo ) )

  disjoint A j
  disjoint A k
  disjoint j k
  disjoint B k
  disjoint C j
  disjoint W j
  disjoint W k
  disjoint j ph
  disjoint k ph
  disjoint A f
  disjoint A l
  disjoint A z
  disjoint f j
  disjoint f k
  disjoint f l
  disjoint f z
  disjoint j l
  disjoint j z
  disjoint k l
  disjoint k z
  disjoint l z
  disjoint B f
  disjoint B l
  disjoint B z
  disjoint C f
  disjoint C z
  disjoint f ph
  disjoint l ph
  disjoint ph z
  assert |- ( ph -> sum* k e. U_ j e. A B C <_ sum* j e. A sum* k e. B C )

  proof
    wph
    vj
    cA
    cB
    ciun
    #
    vf
    cv
    #
    crn
    #
    @1
    wf1o
    #
    vl
    cv
    #
    @1
    cfv
    #
    c2nd
    cfv
    #
    @4
    wceq
    #
    vl
    @0
    wral
    #
    wa
    #
    @2
    vj
    cA
    vj
    cv
    #
    csn
    #
    cB
    cxp
    #
    ciun
    #
    wss
    #
    wa
    #
    @0
    cC
    vk
    cesum
    #
    cA
    cB
    cC
    vk
    cesum
    vj
    cesum
    #
    cle
    wbr
    vf
    wph
    @0
    @13
    @1
    wf1
    #
    @8
    wa
    #
    vf
    wex
    @15
    vf
    wex
    wph
    cA
    cB
    vf
    vj
    vl
    cV
    cW
    esumiun.0
    esumiun.1
    aciunf1
    @19
    @15
    vf
    @19
    @9
    @14
    @18
    @3
    @8
    @0
    @13
    @1
    f1f1orn
    anim1i
    @18
    @14
    @8
    @18
    @0
    @13
    @1
    wf
    @14
    @0
    @13
    @1
    f1f
    @0
    @13
    @1
    frn
    syl
    adantr
    jca
    eximi
    syl
    wph
    @15
    wa
    #
    @16
    @13
    vk
    vz
    cv
    #
    c2nd
    cfv
    #
    cC
    csb
    #
    vz
    cesum
    #
    @17
    cle
    @20
    @2
    @23
    vz
    cesum
    #
    @16
    @24
    cle
    @20
    @16
    @25
    @20
    @0
    cC
    @2
    @23
    vk
    vz
    @1
    ccnv
    #
    @22
    cvv
    @20
    vz
    nfv
    #
    vz
    cC
    nfcv
    vk
    @22
    cC
    nfcsb1v
    #
    vz
    @0
    nfcv
    vz
    @2
    nfcv
    vz
    @26
    nfcv
    vk
    @22
    cC
    csbeq1a
    #
    wph
    @0
    cvv
    wcel
    #
    @15
    wph
    cA
    cV
    wcel
    #
    cB
    cW
    wcel
    #
    vj
    cA
    wral
    @30
    esumiun.0
    wph
    @32
    vj
    cA
    esumiun.1
    ralrimiva
    vj
    cA
    cB
    cV
    cW
    iunexg
    syl2anc
    adantr
    wph
    @3
    @14
    @2
    @0
    @26
    wf1o
    #
    @8
    wph
    @3
    @14
    wa
    wa
    @3
    @33
    wph
    @3
    @14
    simprl
    @0
    @2
    @1
    f1ocnv
    syl
    adantrlr
    @20
    @21
    @2
    wcel
    #
    wa
    #
    @21
    @12
    wcel
    #
    @21
    @26
    cfv
    #
    @22
    wceq
    #
    vj
    cA
    @20
    @34
    vj
    wph
    @15
    vj
    wph
    vj
    nfv
    #
    @9
    @14
    vj
    @3
    @8
    vj
    vj
    @0
    @2
    @1
    vj
    @1
    nfcv
    #
    vj
    cA
    cB
    nfiu1
    #
    vj
    @1
    @40
    nfrn
    nff1o
    @7
    vj
    vl
    @0
    @41
    @7
    vj
    nfv
    nfral
    nfan
    vj
    @2
    @13
    vj
    @2
    nfcv
    vj
    cA
    @12
    nfiu1
    #
    nfss
    nfan
    nfan
    @34
    vj
    nfv
    nfan
    @35
    @10
    cA
    wcel
    #
    wa
    @36
    wa
    #
    vk
    cv
    #
    @1
    cfv
    #
    @21
    wceq
    #
    @38
    vk
    @0
    @44
    @45
    @0
    wcel
    #
    wa
    #
    @47
    wa
    #
    @22
    @45
    @46
    @26
    cfv
    #
    @37
    @50
    @46
    c2nd
    cfv
    #
    @22
    @45
    @50
    @46
    @21
    c2nd
    @49
    @47
    simpr
    #
    fveq2d
    @50
    @48
    @8
    @52
    @45
    wceq
    #
    @44
    @48
    @47
    simplr
    #
    @44
    @8
    @48
    @47
    @44
    @3
    @8
    @44
    @9
    @14
    wph
    @15
    @34
    @43
    @36
    simp-4r
    simpld
    #
    simprd
    ad2antrr
    @7
    @54
    vl
    @45
    @0
    @4
    @45
    wceq
    #
    @6
    @52
    @4
    @45
    @57
    @5
    @46
    c2nd
    @4
    @45
    @1
    fveq2
    fveq2d
    @57
    id
    eqeq12d
    rspcva
    syl2anc
    eqtr3d
    @50
    @3
    @48
    @51
    @45
    wceq
    @44
    @3
    @48
    @47
    @44
    @3
    @8
    @56
    simpld
    #
    ad2antrr
    @55
    @0
    @2
    @45
    @1
    f1ocnvfv1
    syl2anc
    @50
    @46
    @21
    @26
    @53
    fveq2d
    3eqtr2rd
    @44
    @1
    @0
    wfn
    #
    @34
    @47
    vk
    @0
    wrex
    #
    @44
    @3
    @59
    @58
    @0
    @2
    @1
    f1ofn
    syl
    @20
    @34
    @43
    @36
    simpllr
    @59
    @34
    @60
    vk
    @0
    @21
    @1
    fvelrnb
    biimpa
    syl2anc
    r19.29a
    @35
    @21
    @13
    wcel
    #
    @36
    vj
    cA
    wrex
    #
    @20
    @2
    @13
    @21
    wph
    @9
    @14
    simprr
    sselda
    vj
    @21
    cA
    @12
    eliun
    #
    sylib
    r19.29af
    wph
    @48
    cC
    cc0
    cpnf
    cicc
    co
    #
    wcel
    #
    @15
    wph
    @48
    wa
    @45
    cB
    wcel
    #
    @65
    vj
    cA
    wph
    @48
    vj
    @39
    vj
    @45
    @0
    vj
    @45
    nfcv
    @41
    nfel
    nfan
    wph
    @43
    @66
    @65
    @48
    esumiun.2
    adantllr
    @48
    @66
    vj
    cA
    wrex
    #
    wph
    @48
    @67
    vj
    @45
    cA
    cB
    eliun
    biimpi
    adantl
    r19.29af
    adantlr
    esumf1o
    eqcomd
    @20
    @2
    @23
    @13
    vz
    cvv
    @27
    wph
    @13
    cvv
    wcel
    #
    @15
    wph
    @31
    @12
    cvv
    wcel
    #
    vj
    cA
    wral
    @68
    esumiun.0
    wph
    @69
    vj
    cA
    wph
    @43
    wa
    #
    @11
    cvv
    wcel
    #
    @32
    @69
    @71
    @70
    @10
    snex
    a1i
    esumiun.1
    @11
    cB
    cvv
    cW
    xpexg
    syl2anc
    ralrimiva
    vj
    cA
    @12
    cV
    cvv
    iunexg
    syl2anc
    adantr
    wph
    @61
    @23
    @64
    wcel
    #
    @15
    wph
    @61
    wa
    #
    @21
    c1st
    cfv
    #
    @10
    wceq
    #
    @22
    cB
    wcel
    #
    wa
    #
    @72
    vj
    cA
    wph
    @61
    vj
    @39
    vj
    @21
    @13
    vj
    @21
    nfcv
    @42
    nfel
    nfan
    vj
    @23
    @64
    vj
    vk
    @22
    cC
    vj
    @22
    nfcv
    vj
    cC
    nfcv
    nfcsb
    vj
    @64
    nfcv
    nfel
    @73
    @43
    wa
    #
    @77
    wa
    #
    @76
    @65
    vk
    cB
    wral
    #
    @72
    @78
    @75
    @76
    simprr
    @79
    wph
    @43
    @80
    wph
    @61
    @43
    @77
    simplll
    @73
    @43
    @77
    simplr
    @70
    @65
    vk
    cB
    esumiun.2
    ralrimiva
    syl2anc
    vk
    @22
    cB
    cC
    @64
    rspcsbela
    syl2anc
    @61
    @77
    vj
    cA
    wrex
    #
    wph
    @61
    @62
    @81
    @63
    @36
    @77
    vj
    cA
    @36
    @75
    @76
    @36
    @74
    @11
    wcel
    @75
    @21
    @11
    cB
    xp1st
    @74
    @10
    elsni
    syl
    @21
    @11
    cB
    xp2nd
    jca
    reximi
    sylbi
    adantl
    r19.29af2
    adantlr
    wph
    @3
    @14
    @14
    @8
    wph
    @3
    @14
    simprr
    adantrlr
    esummono
    eqbrtrrd
    wph
    @17
    @24
    wceq
    @15
    wph
    vz
    cA
    cB
    cC
    vj
    vk
    @23
    cV
    cW
    @28
    @21
    @10
    @45
    cop
    wceq
    #
    cC
    @23
    @82
    @45
    @22
    wceq
    cC
    @23
    wceq
    @82
    @22
    @45
    @10
    @45
    @21
    vj
    vex
    vk
    vex
    op2ndd
    eqcomd
    @29
    syl
    eqcomd
    esumiun.0
    esumiun.1
    wph
    @43
    @66
    @65
    esumiun.2
    anasss
    esum2d
    adantr
    breqtrrd
    exlimddv
end
