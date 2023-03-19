include "caddc.mm"
include "cabs.mm"
include "cmin.mm"
include "ccom.mm"
include "c1.mm"
include "cseq.mm"
include "crn.mm"
include "cxr.mm"
include "clt.mm"
include "csup.mm"
include "cn.mm"
include "cle.mm"
include "cr.mm"
include "cxp.mm"
include "cin.mm"
include "wf.mm"
include "cc0.mm"
include "cpnf.mm"
include "cico.mm"
include "co.mm"
include "wfn.mm"
include "cv.mm"
include "cfv.mm"
include "c1st.mm"
include "c2nd.mm"
include "cop.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "w3a.mm"
include "ovolfcl.mm"
include "sylan.mm"
include "simp1d.mm"
include "simp2d.mm"
include "adantr.mm"
include "simp3d.mm"
include "leadd1dd.mm"
include "df-br.mm"
include "sylib.mm"
include "readdcld.mm"
include "opelxp.mm"
include "sylanbrc.mm"
include "elind.mm"
include "fmptd.mm"
include "eqid.mm"
include "ovolfsf.mm"
include "ffn.mm"
include "3syl.mm"
include "wceq.mm"
include "cvv.mm"
include "opex.mm"
include "fvmpt2.mm"
include "mpan2.mm"
include "fveq2d.mm"
include "ovex.mm"
include "op2nd.mm"
include "syl6eq.mm"
include "op1st.mm"
include "oveq12d.mm"
include "adantl.mm"
include "recnd.mm"
include "pnpcan2d.mm"
include "eqtrd.mm"
include "ovolfsval.mm"
include "3eqtr4d.mm"
include "eqfnfvd.mm"
include "seqeq3d.mm"
include "syl6eqr.mm"
include "rneqd.mm"
include "supeq1d.mm"
include "cioo.mm"
include "cuni.mm"
include "wss.mm"
include "wrex.mm"
include "wral.mm"
include "crab.mm"
include "eleq2d.mm"
include "oveq1.mm"
include "eleq1d.mm"
include "elrab.mm"
include "syl6bb.mm"
include "biimpa.mm"
include "simprr.mm"
include "wb.mm"
include "ovolfioo.mm"
include "syl2anc.mm"
include "mpbid.mm"
include "breq2.mm"
include "breq1.mm"
include "anbi12d.mm"
include "rexbidv.mm"
include "rspcv.mm"
include "sylc.mm"
include "breq1d.mm"
include "adantlr.mm"
include "ad2antrr.mm"
include "simplrl.mm"
include "ltaddsubd.mm"
include "bitrd.mm"
include "breq2d.mm"
include "ltsubaddd.mm"
include "bitr4d.mm"
include "rexbidva.mm"
include "mpbird.mm"
include "syldan.mm"
include "ralrimiva.mm"
include "ssrab2.mm"
include "syl6eqss.mm"
include "elovolmr.mm"
include "eqeltrrd.mm"

theorem ovolshftlem1
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cS: class S
  let vf: setvar f
  let vn: setvar n
  let cF: class F
  let cG: class G
  let cM: class M
  let vg: setvar g
  let vw: setvar w
  let vz: setvar z
  let vm: setvar m
  assume ovolshft.1: |- ( ph -> A C_ RR )
  assume ovolshft.2: |- ( ph -> C e. RR )
  assume ovolshft.3: |- ( ph -> B = { x e. RR | ( x - C ) e. A } )
  assume ovolshft.4: |- M = { y e. RR* | E. f e. ( ( <_ i^i ( RR X. RR ) ) ^m NN ) ( B C_ U. ran ( (,) o. f ) /\ y = sup ( ran seq 1 ( + , ( ( abs o. - ) o. f ) ) , RR* , < ) ) }
  assume ovolshft.5: |- S = seq 1 ( + , ( ( abs o. - ) o. F ) )
  assume ovolshft.6: |- G = ( n e. NN |-> <. ( ( 1st ` ( F ` n ) ) + C ) , ( ( 2nd ` ( F ` n ) ) + C ) >. )
  assume ovolshft.7: |- ( ph -> F : NN --> ( <_ i^i ( RR X. RR ) ) )
  assume ovolshft.8: |- ( ph -> A C_ U. ran ( (,) o. F ) )

  disjoint f n
  disjoint f x
  disjoint f y
  disjoint A f
  disjoint n x
  disjoint n y
  disjoint A n
  disjoint x y
  disjoint A x
  disjoint A y
  disjoint C f
  disjoint C n
  disjoint C x
  disjoint C y
  disjoint F n
  disjoint F x
  disjoint G f
  disjoint G n
  disjoint G y
  disjoint B f
  disjoint B n
  disjoint B y
  disjoint f ph
  disjoint n ph
  disjoint ph y
  disjoint f g
  disjoint f w
  disjoint f z
  disjoint g n
  disjoint g w
  disjoint g x
  disjoint g y
  disjoint g z
  disjoint A g
  disjoint n w
  disjoint n z
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint A w
  disjoint x z
  disjoint y z
  disjoint A z
  disjoint f m
  disjoint g m
  disjoint C g
  disjoint m n
  disjoint m w
  disjoint m x
  disjoint m y
  disjoint m z
  disjoint C m
  disjoint C w
  disjoint C z
  disjoint B g
  disjoint B w
  disjoint B z
  disjoint M g
  disjoint M z
  disjoint g ph
  disjoint ph w
  disjoint ph z
  assert |- ( ph -> sup ( ran S , RR* , < ) e. M )

  proof
    wph
    caddc
    cabs
    cmin
    ccom
    #
    cG
    ccom
    #
    c1
    cseq
    #
    crn
    #
    cxr
    clt
    csup
    #
    cS
    crn
    #
    cxr
    clt
    csup
    cM
    wph
    cxr
    @3
    @5
    clt
    wph
    @2
    cS
    wph
    @2
    caddc
    @0
    cF
    ccom
    #
    c1
    cseq
    cS
    wph
    @1
    @6
    caddc
    c1
    wph
    vn
    cn
    @1
    @6
    wph
    cn
    cle
    cr
    cr
    cxp
    #
    cin
    #
    cG
    wf
    #
    cn
    cc0
    cpnf
    cico
    co
    #
    @1
    wf
    @1
    cn
    wfn
    wph
    vn
    cn
    vn
    cv
    #
    cF
    cfv
    #
    c1st
    cfv
    #
    cC
    caddc
    co
    #
    @12
    c2nd
    cfv
    #
    cC
    caddc
    co
    #
    cop
    #
    @8
    cG
    wph
    @11
    cn
    wcel
    #
    wa
    #
    cle
    @7
    @17
    @19
    @14
    @16
    cle
    wbr
    @17
    cle
    wcel
    @19
    @13
    @15
    cC
    @19
    @13
    cr
    wcel
    #
    @15
    cr
    wcel
    #
    @13
    @15
    cle
    wbr
    #
    wph
    cn
    @8
    cF
    wf
    #
    @18
    @20
    @21
    @22
    w3a
    ovolshft.7
    cF
    @11
    ovolfcl
    sylan
    #
    simp1d
    #
    @19
    @20
    @21
    @22
    @24
    simp2d
    #
    wph
    cC
    cr
    wcel
    #
    @18
    ovolshft.2
    adantr
    #
    @19
    @20
    @21
    @22
    @24
    simp3d
    leadd1dd
    @14
    @16
    cle
    df-br
    sylib
    @19
    @14
    cr
    wcel
    @16
    cr
    wcel
    @17
    @7
    wcel
    @19
    @13
    cC
    @25
    @28
    readdcld
    @19
    @15
    cC
    @26
    @28
    readdcld
    @14
    @16
    cr
    cr
    opelxp
    sylanbrc
    elind
    ovolshft.6
    fmptd
    #
    cG
    @1
    @1
    eqid
    #
    ovolfsf
    cn
    @10
    @1
    ffn
    3syl
    wph
    @23
    cn
    @10
    @6
    wf
    @6
    cn
    wfn
    ovolshft.7
    cF
    @6
    @6
    eqid
    #
    ovolfsf
    cn
    @10
    @6
    ffn
    3syl
    @19
    @11
    cG
    cfv
    #
    c2nd
    cfv
    #
    @32
    c1st
    cfv
    #
    cmin
    co
    #
    @15
    @13
    cmin
    co
    #
    @11
    @1
    cfv
    #
    @11
    @6
    cfv
    #
    @19
    @35
    @16
    @14
    cmin
    co
    #
    @36
    @18
    @35
    @39
    wceq
    wph
    @18
    @33
    @16
    @34
    @14
    cmin
    @18
    @33
    @17
    c2nd
    cfv
    @16
    @18
    @32
    @17
    c2nd
    @18
    @17
    cvv
    wcel
    @32
    @17
    wceq
    @14
    @16
    opex
    vn
    cn
    @17
    cvv
    cG
    ovolshft.6
    fvmpt2
    mpan2
    #
    fveq2d
    @14
    @16
    @13
    cC
    caddc
    ovex
    #
    @15
    cC
    caddc
    ovex
    #
    op2nd
    syl6eq
    #
    @18
    @34
    @17
    c1st
    cfv
    @14
    @18
    @32
    @17
    c1st
    @40
    fveq2d
    @14
    @16
    @41
    @42
    op1st
    syl6eq
    #
    oveq12d
    adantl
    @19
    @15
    @13
    cC
    @19
    @15
    @26
    recnd
    @19
    @13
    @25
    recnd
    @19
    cC
    @28
    recnd
    pnpcan2d
    eqtrd
    wph
    @9
    @18
    @37
    @35
    wceq
    @29
    cG
    @1
    @11
    @30
    ovolfsval
    sylan
    wph
    @23
    @18
    @38
    @36
    wceq
    ovolshft.7
    cF
    @6
    @11
    @31
    ovolfsval
    sylan
    3eqtr4d
    eqfnfvd
    seqeq3d
    ovolshft.5
    syl6eqr
    rneqd
    supeq1d
    wph
    @9
    cB
    cioo
    cG
    ccom
    crn
    cuni
    wss
    #
    @4
    cM
    wcel
    @29
    wph
    @45
    @34
    vy
    cv
    #
    clt
    wbr
    #
    @46
    @33
    clt
    wbr
    #
    wa
    #
    vn
    cn
    wrex
    #
    vy
    cB
    wral
    #
    wph
    @50
    vy
    cB
    wph
    @46
    cB
    wcel
    #
    @46
    cr
    wcel
    #
    @46
    cC
    cmin
    co
    #
    cA
    wcel
    #
    wa
    #
    @50
    wph
    @52
    @56
    wph
    @52
    @46
    vx
    cv
    #
    cC
    cmin
    co
    #
    cA
    wcel
    #
    vx
    cr
    crab
    #
    wcel
    @56
    wph
    cB
    @60
    @46
    ovolshft.3
    eleq2d
    @59
    @55
    vx
    @46
    cr
    @57
    @46
    wceq
    @58
    @54
    cA
    @57
    @46
    cC
    cmin
    oveq1
    eleq1d
    elrab
    syl6bb
    biimpa
    wph
    @56
    wa
    #
    @50
    @13
    @54
    clt
    wbr
    #
    @54
    @15
    clt
    wbr
    #
    wa
    #
    vn
    cn
    wrex
    #
    @61
    @55
    @13
    @57
    clt
    wbr
    #
    @57
    @15
    clt
    wbr
    #
    wa
    #
    vn
    cn
    wrex
    #
    vx
    cA
    wral
    #
    @65
    wph
    @53
    @55
    simprr
    wph
    @70
    @56
    wph
    cA
    cioo
    cF
    ccom
    crn
    cuni
    wss
    #
    @70
    ovolshft.8
    wph
    cA
    cr
    wss
    @23
    @71
    @70
    wb
    ovolshft.1
    ovolshft.7
    vx
    cA
    vn
    cF
    ovolfioo
    syl2anc
    mpbid
    adantr
    @69
    @65
    vx
    @54
    cA
    @57
    @54
    wceq
    #
    @68
    @64
    vn
    cn
    @72
    @66
    @62
    @67
    @63
    @57
    @54
    @13
    clt
    breq2
    @57
    @54
    @15
    clt
    breq1
    anbi12d
    rexbidv
    rspcv
    sylc
    @61
    @49
    @64
    vn
    cn
    @61
    @18
    wa
    #
    @47
    @62
    @48
    @63
    @73
    @47
    @14
    @46
    clt
    wbr
    @62
    @73
    @34
    @14
    @46
    clt
    @18
    @34
    @14
    wceq
    @61
    @44
    adantl
    breq1d
    @73
    @13
    cC
    @46
    wph
    @18
    @20
    @56
    @25
    adantlr
    wph
    @27
    @56
    @18
    ovolshft.2
    ad2antrr
    #
    wph
    @53
    @55
    @18
    simplrl
    #
    ltaddsubd
    bitrd
    @73
    @48
    @46
    @16
    clt
    wbr
    @63
    @73
    @33
    @16
    @46
    clt
    @18
    @33
    @16
    wceq
    @61
    @43
    adantl
    breq2d
    @73
    @46
    cC
    @15
    @75
    @74
    wph
    @18
    @21
    @56
    @26
    adantlr
    ltsubaddd
    bitr4d
    anbi12d
    rexbidva
    mpbird
    syldan
    ralrimiva
    wph
    cB
    cr
    wss
    @9
    @45
    @51
    wb
    wph
    cB
    @60
    cr
    ovolshft.3
    @59
    vx
    cr
    ssrab2
    syl6eqss
    @29
    vy
    cB
    vn
    cG
    ovolfioo
    syl2anc
    mpbird
    vy
    cB
    @2
    vf
    cG
    cM
    ovolshft.4
    @2
    eqid
    elovolmr
    syl2anc
    eqeltrrd
end
