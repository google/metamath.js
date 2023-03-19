include "cicc.mm"
include "co.mm"
include "covol.mm"
include "cfv.mm"
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
include "cr.mm"
include "wss.mm"
include "wcel.mm"
include "iccssre.mm"
include "syl2anc.mm"
include "ovolcl.mm"
include "syl.mm"
include "cc0.mm"
include "cpnf.mm"
include "cico.mm"
include "cn.mm"
include "wf.mm"
include "cle.mm"
include "cxp.mm"
include "cin.mm"
include "cv.mm"
include "wceq.mm"
include "cop.mm"
include "cif.mm"
include "wa.mm"
include "wbr.mm"
include "df-br.mm"
include "sylib.mm"
include "opelxpi.mm"
include "elind.mm"
include "adantr.mm"
include "0le0.mm"
include "mpbi.mm"
include "0re.mm"
include "mp2an.mm"
include "elin.mm"
include "mpbir2an.mm"
include "ifcl.mm"
include "sylancl.mm"
include "fmptd.mm"
include "eqid.mm"
include "ovolsf.mm"
include "frn.mm"
include "icossxr.mm"
include "syl6ss.mm"
include "supxrcl.mm"
include "resubcld.mm"
include "rexrd.mm"
include "cuni.mm"
include "c1st.mm"
include "c2nd.mm"
include "wrex.mm"
include "wral.mm"
include "1nn.mm"
include "a1i.mm"
include "op1stg.mm"
include "w3a.mm"
include "wb.mm"
include "elicc2.mm"
include "biimpa.mm"
include "simp2d.mm"
include "eqbrtrd.mm"
include "simp3d.mm"
include "op2ndg.mm"
include "breqtrrd.mm"
include "fveq2.mm"
include "iftrue.mm"
include "opex.mm"
include "fvmpt.mm"
include "ax-mp.mm"
include "syl6eq.mm"
include "fveq2d.mm"
include "breq1d.mm"
include "breq2d.mm"
include "anbi12d.mm"
include "rspcev.mm"
include "syl12anc.mm"
include "ralrimiva.mm"
include "ovolficc.mm"
include "mpbird.mm"
include "ovollb2.mm"
include "cc.mm"
include "addid1.mm"
include "adantl.mm"
include "cuz.mm"
include "nnuz.mm"
include "eleqtri.mm"
include "simpr.mm"
include "syl6eleq.mm"
include "rge0ssre.mm"
include "ffvelrn.mm"
include "sseldi.mm"
include "recnd.mm"
include "cfz.mm"
include "ad2antrr.mm"
include "c2.mm"
include "elfzuz.mm"
include "df-2.mm"
include "fveq2i.mm"
include "syl6eleqr.mm"
include "eluz2nn.mm"
include "ovolfsval.mm"
include "eqeq1.mm"
include "ifbid.mm"
include "ifex.mm"
include "wne.mm"
include "eluz2b3.mm"
include "simprbi.mm"
include "neneqd.mm"
include "iffalsed.mm"
include "eqtrd.mm"
include "c0ex.mm"
include "op2nd.mm"
include "op1st.mm"
include "oveq12d.mm"
include "0m0e0.mm"
include "seqid2.mm"
include "1z.mm"
include "syl5eq.mm"
include "seq1i.mm"
include "eqtr3d.mm"
include "leidd.mm"
include "wfn.mm"
include "ffn.mm"
include "breq1.mm"
include "ralrn.mm"
include "supxrleub.mm"
include "xrletrd.mm"

theorem ovolicc1
  let wph: wff ph
  let cA: class A
  let cB: class B
  let vn: setvar n
  let cG: class G
  let vf: setvar f
  let vg: setvar g
  let vh: setvar h
  let vk: setvar k
  let vm: setvar m
  let vt: setvar t
  let vu: setvar u
  let vv: setvar v
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cH: class H
  let cC: class C
  let vi: setvar i
  let vj: setvar j
  let cF: class F
  let cK: class K
  let cM: class M
  let cW: class W
  let cP: class P
  let cT: class T
  let cN: class N
  let cS: class S
  let cU: class U
  let cX: class X
  assume ovolicc.1: |- ( ph -> A e. RR )
  assume ovolicc.2: |- ( ph -> B e. RR )
  assume ovolicc.3: |- ( ph -> A <_ B )
  assume ovolicc1.4: |- G = ( n e. NN |-> if ( n = 1 , <. A , B >. , <. 0 , 0 >. ) )

  disjoint A n
  disjoint B n
  disjoint G n
  disjoint n ph
  disjoint f g
  disjoint f h
  disjoint f k
  disjoint f m
  disjoint f n
  disjoint f t
  disjoint f u
  disjoint f v
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint A f
  disjoint g h
  disjoint g k
  disjoint g m
  disjoint g n
  disjoint g t
  disjoint g u
  disjoint g v
  disjoint g x
  disjoint g y
  disjoint g z
  disjoint A g
  disjoint h k
  disjoint h m
  disjoint h n
  disjoint h t
  disjoint h u
  disjoint h v
  disjoint h x
  disjoint h y
  disjoint h z
  disjoint A h
  disjoint k m
  disjoint k n
  disjoint k t
  disjoint k u
  disjoint k v
  disjoint k x
  disjoint k y
  disjoint k z
  disjoint A k
  disjoint m n
  disjoint m t
  disjoint m u
  disjoint m v
  disjoint m x
  disjoint m y
  disjoint m z
  disjoint A m
  disjoint n t
  disjoint n u
  disjoint n v
  disjoint n x
  disjoint n y
  disjoint n z
  disjoint t u
  disjoint t v
  disjoint t x
  disjoint t y
  disjoint t z
  disjoint A t
  disjoint u v
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint A u
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint A v
  disjoint x y
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint B f
  disjoint B g
  disjoint B h
  disjoint B k
  disjoint B m
  disjoint B t
  disjoint B u
  disjoint B v
  disjoint B x
  disjoint B y
  disjoint B z
  disjoint H t
  disjoint C f
  disjoint C g
  disjoint C k
  disjoint C m
  disjoint C n
  disjoint C t
  disjoint C y
  disjoint C z
  disjoint h i
  disjoint h j
  disjoint F h
  disjoint i j
  disjoint i k
  disjoint i n
  disjoint i t
  disjoint i x
  disjoint i y
  disjoint F i
  disjoint j k
  disjoint j n
  disjoint j t
  disjoint j x
  disjoint j y
  disjoint F j
  disjoint F k
  disjoint F n
  disjoint F t
  disjoint F x
  disjoint F y
  disjoint i u
  disjoint i z
  disjoint K i
  disjoint j u
  disjoint j z
  disjoint K j
  disjoint K k
  disjoint K n
  disjoint K t
  disjoint K u
  disjoint K x
  disjoint K y
  disjoint K z
  disjoint f i
  disjoint f j
  disjoint G f
  disjoint G h
  disjoint G i
  disjoint G j
  disjoint G k
  disjoint G t
  disjoint G x
  disjoint G y
  disjoint G z
  disjoint i m
  disjoint M i
  disjoint j m
  disjoint M j
  disjoint M m
  disjoint M n
  disjoint M t
  disjoint M x
  disjoint M y
  disjoint M z
  disjoint W i
  disjoint W j
  disjoint W k
  disjoint W m
  disjoint W n
  disjoint W x
  disjoint W y
  disjoint P k
  disjoint P y
  disjoint f ph
  disjoint g i
  disjoint g j
  disjoint g ph
  disjoint h ph
  disjoint i v
  disjoint i ph
  disjoint j v
  disjoint j ph
  disjoint k ph
  disjoint m ph
  disjoint ph t
  disjoint ph v
  disjoint ph x
  disjoint ph y
  disjoint ph z
  disjoint T f
  disjoint T h
  disjoint T k
  disjoint T n
  disjoint T t
  disjoint T x
  disjoint T y
  disjoint T z
  disjoint N k
  disjoint N n
  disjoint N t
  disjoint N u
  disjoint N x
  disjoint N y
  disjoint S h
  disjoint S z
  disjoint U h
  disjoint U n
  disjoint U t
  disjoint U u
  disjoint U x
  disjoint U z
  disjoint X t
  assert |- ( ph -> ( vol* ` ( A [,] B ) ) <_ ( B - A ) )

  proof
    wph
    cA
    cB
    cicc
    co
    #
    covol
    cfv
    #
    caddc
    cabs
    cmin
    ccom
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
    cB
    cA
    cmin
    co
    #
    wph
    @0
    cr
    wss
    #
    @1
    cxr
    wcel
    wph
    cA
    cr
    wcel
    #
    cB
    cr
    wcel
    #
    @7
    ovolicc.1
    ovolicc.2
    cA
    cB
    iccssre
    syl2anc
    #
    @0
    ovolcl
    syl
    wph
    @4
    cxr
    wss
    #
    @5
    cxr
    wcel
    wph
    @4
    cc0
    cpnf
    cico
    co
    #
    cxr
    wph
    cn
    @12
    @3
    wf
    #
    @4
    @12
    wss
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
    @13
    wph
    vn
    cn
    vn
    cv
    #
    c1
    wceq
    #
    cA
    cB
    cop
    #
    cc0
    cc0
    cop
    #
    cif
    #
    @15
    cG
    wph
    @17
    cn
    wcel
    #
    wa
    @19
    @15
    wcel
    #
    @20
    @15
    wcel
    #
    @21
    @15
    wcel
    wph
    @23
    @22
    wph
    cle
    @14
    @19
    wph
    cA
    cB
    cle
    wbr
    @19
    cle
    wcel
    ovolicc.3
    cA
    cB
    cle
    df-br
    sylib
    wph
    @8
    @9
    @19
    @14
    wcel
    ovolicc.1
    ovolicc.2
    cA
    cB
    cr
    cr
    opelxpi
    syl2anc
    elind
    adantr
    @24
    @20
    cle
    wcel
    #
    @20
    @14
    wcel
    #
    cc0
    cc0
    cle
    wbr
    @25
    0le0
    cc0
    cc0
    cle
    df-br
    mpbi
    cc0
    cr
    wcel
    #
    @27
    @26
    0re
    0re
    cc0
    cc0
    cr
    cr
    opelxpi
    mp2an
    @20
    cle
    @14
    elin
    mpbir2an
    @18
    @19
    @20
    @15
    ifcl
    sylancl
    ovolicc1.4
    fmptd
    #
    @3
    cG
    @2
    @2
    eqid
    #
    @3
    eqid
    #
    ovolsf
    syl
    #
    cn
    @12
    @3
    frn
    syl
    cc0
    cpnf
    icossxr
    syl6ss
    #
    @4
    supxrcl
    syl
    wph
    @6
    wph
    cB
    cA
    ovolicc.2
    ovolicc.1
    resubcld
    #
    rexrd
    #
    wph
    @16
    @0
    cicc
    cG
    ccom
    crn
    cuni
    wss
    #
    @1
    @5
    cle
    wbr
    @28
    wph
    @35
    @17
    cG
    cfv
    #
    c1st
    cfv
    #
    vx
    cv
    #
    cle
    wbr
    #
    @38
    @36
    c2nd
    cfv
    #
    cle
    wbr
    #
    wa
    #
    vn
    cn
    wrex
    #
    vx
    @0
    wral
    #
    wph
    @43
    vx
    @0
    wph
    @38
    @0
    wcel
    #
    wa
    #
    c1
    cn
    wcel
    #
    @19
    c1st
    cfv
    #
    @38
    cle
    wbr
    #
    @38
    @19
    c2nd
    cfv
    #
    cle
    wbr
    #
    @43
    @47
    @46
    1nn
    a1i
    @46
    @48
    cA
    @38
    cle
    wph
    @48
    cA
    wceq
    #
    @45
    wph
    @8
    @9
    @52
    ovolicc.1
    ovolicc.2
    cA
    cB
    cr
    cr
    op1stg
    syl2anc
    #
    adantr
    @46
    @38
    cr
    wcel
    #
    cA
    @38
    cle
    wbr
    #
    @38
    cB
    cle
    wbr
    #
    wph
    @45
    @54
    @55
    @56
    w3a
    #
    wph
    @8
    @9
    @45
    @57
    wb
    ovolicc.1
    ovolicc.2
    cA
    cB
    @38
    elicc2
    syl2anc
    biimpa
    #
    simp2d
    eqbrtrd
    @46
    @38
    cB
    @50
    cle
    @46
    @54
    @55
    @56
    @58
    simp3d
    wph
    @50
    cB
    wceq
    #
    @45
    wph
    @8
    @9
    @59
    ovolicc.1
    ovolicc.2
    cA
    cB
    cr
    cr
    op2ndg
    syl2anc
    #
    adantr
    breqtrrd
    @42
    @49
    @51
    wa
    vn
    c1
    cn
    @18
    @39
    @49
    @41
    @51
    @18
    @37
    @48
    @38
    cle
    @18
    @36
    @19
    c1st
    @18
    @36
    c1
    cG
    cfv
    #
    @19
    @17
    c1
    cG
    fveq2
    @47
    @61
    @19
    wceq
    1nn
    vn
    c1
    @21
    @19
    cn
    cG
    @18
    @19
    @20
    iftrue
    ovolicc1.4
    cA
    cB
    opex
    #
    fvmpt
    ax-mp
    #
    syl6eq
    #
    fveq2d
    breq1d
    @18
    @40
    @50
    @38
    cle
    @18
    @36
    @19
    c2nd
    @64
    fveq2d
    breq2d
    anbi12d
    rspcev
    syl12anc
    ralrimiva
    wph
    @7
    @16
    @35
    @44
    wb
    @10
    @28
    vx
    @0
    vn
    cG
    ovolficc
    syl2anc
    mpbird
    @0
    @3
    cG
    @30
    ovollb2
    syl2anc
    wph
    @5
    @6
    cle
    wbr
    #
    vz
    cv
    #
    @6
    cle
    wbr
    #
    vz
    @4
    wral
    #
    wph
    @68
    @38
    @3
    cfv
    #
    @6
    cle
    wbr
    #
    vx
    cn
    wral
    #
    wph
    @70
    vx
    cn
    wph
    @38
    cn
    wcel
    #
    wa
    #
    @69
    @6
    @6
    cle
    @73
    c1
    @3
    cfv
    #
    @69
    @6
    @73
    vk
    caddc
    cc
    @2
    c1
    c1
    @38
    cc0
    vk
    cv
    #
    cc
    wcel
    @75
    cc0
    caddc
    co
    @75
    wceq
    @73
    @75
    addid1
    adantl
    c1
    c1
    cuz
    cfv
    #
    wcel
    @73
    c1
    cn
    @76
    1nn
    nnuz
    eleqtri
    a1i
    @73
    @38
    cn
    @76
    wph
    @72
    simpr
    nnuz
    syl6eleq
    @73
    @74
    @73
    @12
    cr
    @74
    rge0ssre
    @73
    @13
    @47
    @74
    @12
    wcel
    wph
    @13
    @72
    @31
    adantr
    1nn
    cn
    @12
    c1
    @3
    ffvelrn
    sylancl
    sseldi
    recnd
    @73
    @75
    c1
    c1
    caddc
    co
    #
    @38
    cfz
    co
    wcel
    #
    wa
    #
    @75
    @2
    cfv
    #
    @75
    cG
    cfv
    #
    c2nd
    cfv
    #
    @81
    c1st
    cfv
    #
    cmin
    co
    #
    cc0
    @79
    @16
    @75
    cn
    wcel
    #
    @80
    @84
    wceq
    wph
    @16
    @72
    @78
    @28
    ad2antrr
    @79
    @75
    c2
    cuz
    cfv
    #
    wcel
    #
    @85
    @79
    @75
    @77
    cuz
    cfv
    #
    @86
    @78
    @75
    @88
    wcel
    @73
    @75
    @77
    @38
    elfzuz
    adantl
    c2
    @77
    cuz
    df-2
    fveq2i
    syl6eleqr
    #
    @75
    eluz2nn
    syl
    #
    cG
    @2
    @75
    @29
    ovolfsval
    syl2anc
    @79
    @84
    cc0
    cc0
    cmin
    co
    cc0
    @79
    @82
    cc0
    @83
    cc0
    cmin
    @79
    @82
    @20
    c2nd
    cfv
    cc0
    @79
    @81
    @20
    c2nd
    @79
    @81
    @75
    c1
    wceq
    #
    @19
    @20
    cif
    #
    @20
    @79
    @85
    @81
    @92
    wceq
    @90
    vn
    @75
    @21
    @92
    cn
    cG
    @17
    @75
    wceq
    @18
    @91
    @19
    @20
    @17
    @75
    c1
    eqeq1
    ifbid
    ovolicc1.4
    @91
    @19
    @20
    @62
    cc0
    cc0
    opex
    ifex
    fvmpt
    syl
    @79
    @91
    @19
    @20
    @79
    @75
    c1
    @79
    @87
    @75
    c1
    wne
    #
    @89
    @87
    @85
    @93
    @75
    eluz2b3
    simprbi
    syl
    neneqd
    iffalsed
    eqtrd
    #
    fveq2d
    cc0
    cc0
    c0ex
    c0ex
    op2nd
    syl6eq
    @79
    @83
    @20
    c1st
    cfv
    cc0
    @79
    @81
    @20
    c1st
    @94
    fveq2d
    cc0
    cc0
    c0ex
    c0ex
    op1st
    syl6eq
    oveq12d
    0m0e0
    syl6eq
    eqtrd
    seqid2
    @73
    @6
    caddc
    @2
    c1
    1z
    @73
    c1
    @2
    cfv
    #
    @61
    c2nd
    cfv
    #
    @61
    c1st
    cfv
    #
    cmin
    co
    #
    @6
    @73
    @16
    @47
    @95
    @98
    wceq
    wph
    @16
    @72
    @28
    adantr
    1nn
    cG
    @2
    c1
    @29
    ovolfsval
    sylancl
    @73
    @96
    cB
    @97
    cA
    cmin
    @73
    @96
    @50
    cB
    @61
    @19
    c2nd
    @63
    fveq2i
    wph
    @59
    @72
    @60
    adantr
    syl5eq
    @73
    @97
    @48
    cA
    @61
    @19
    c1st
    @63
    fveq2i
    wph
    @52
    @72
    @53
    adantr
    syl5eq
    oveq12d
    eqtrd
    seq1i
    eqtr3d
    wph
    @6
    @6
    cle
    wbr
    @72
    wph
    @6
    @33
    leidd
    adantr
    eqbrtrd
    ralrimiva
    wph
    @3
    cn
    wfn
    #
    @68
    @71
    wb
    wph
    @13
    @99
    @31
    cn
    @12
    @3
    ffn
    syl
    @67
    @70
    vz
    vx
    cn
    @3
    @66
    @69
    @6
    cle
    breq1
    ralrn
    syl
    mpbird
    wph
    @11
    @6
    cxr
    wcel
    @65
    @68
    wb
    @32
    @34
    vz
    @4
    @6
    supxrleub
    syl2anc
    mpbird
    xrletrd
end
