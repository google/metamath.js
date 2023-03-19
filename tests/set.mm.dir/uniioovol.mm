include "cioo.mm"
include "ccom.mm"
include "crn.mm"
include "cuni.mm"
include "covol.mm"
include "cfv.mm"
include "cxr.mm"
include "clt.mm"
include "csup.mm"
include "wceq.mm"
include "cle.mm"
include "wbr.mm"
include "cn.mm"
include "cr.mm"
include "cxp.mm"
include "cin.mm"
include "wf.mm"
include "wss.mm"
include "ssid.mm"
include "ovollb.mm"
include "sylancl.mm"
include "cv.mm"
include "wral.mm"
include "wcel.mm"
include "wa.mm"
include "c1.mm"
include "cfz.mm"
include "co.mm"
include "ciun.mm"
include "cvol.mm"
include "csu.mm"
include "caddc.mm"
include "cabs.mm"
include "cmin.mm"
include "cseq.mm"
include "c2nd.mm"
include "c1st.mm"
include "adantr.mm"
include "elfznn.mm"
include "eqid.mm"
include "ovolfsval.mm"
include "syl2an.mm"
include "cdm.mm"
include "fvco3.mm"
include "cop.mm"
include "inss2.mm"
include "ffvelrn.mm"
include "sseldi.mm"
include "1st2nd2.mm"
include "syl.mm"
include "fveq2d.mm"
include "df-ov.mm"
include "syl6eqr.mm"
include "eqtrd.mm"
include "ioombl.mm"
include "syl6eqel.mm"
include "mblvol.mm"
include "w3a.mm"
include "ovolfcl.mm"
include "ovolioo.mm"
include "3eqtrd.mm"
include "eqtr4d.mm"
include "cuz.mm"
include "simpr.mm"
include "nnuz.mm"
include "syl6eleq.mm"
include "simp2d.mm"
include "simp1d.mm"
include "resubcld.mm"
include "eqeltrd.mm"
include "recnd.mm"
include "fsumser.mm"
include "fveq1i.mm"
include "syl6reqr.mm"
include "cfn.mm"
include "wdisj.mm"
include "fzfid.mm"
include "jca.mm"
include "ralrimiva.mm"
include "ssriv.mm"
include "sylan.mm"
include "disjeq2dv.mm"
include "mpbird.mm"
include "disjss1.mm"
include "mpsyl.mm"
include "volfiniun.mm"
include "syl3anc.mm"
include "finiunmbl.mm"
include "syl2anc.mm"
include "3eqtr2d.mm"
include "iunss1.mm"
include "mp1i.mm"
include "cpw.mm"
include "wfn.mm"
include "ioof.mm"
include "rexpssxrxp.mm"
include "sstri.mm"
include "fss.mm"
include "fco.mm"
include "sylancr.mm"
include "ffn.mm"
include "fniunfv.mm"
include "3syl.mm"
include "sseqtrd.mm"
include "frn.mm"
include "sspwuni.mm"
include "sylib.mm"
include "ovolss.mm"
include "eqbrtrd.mm"
include "cc0.mm"
include "cpnf.mm"
include "cico.mm"
include "wb.mm"
include "ovolsf.mm"
include "breq1.mm"
include "ralrn.mm"
include "icossxr.mm"
include "syl6ss.mm"
include "ovolcl.mm"
include "supxrleub.mm"
include "supxrcl.mm"
include "xrletri3.mm"
include "mpbir2and.mm"

theorem uniioovol
  let wph: wff ph
  let vx: setvar x
  let cS: class S
  let cF: class F
  let va: setvar a
  let vf: setvar f
  let vi: setvar i
  let vj: setvar j
  let vk: setvar k
  let vn: setvar n
  let vr: setvar r
  let vy: setvar y
  let vz: setvar z
  let vm: setvar m
  let vw: setvar w
  let cG: class G
  let cK: class K
  let cA: class A
  let cC: class C
  let cM: class M
  let cE: class E
  let cH: class H
  let cJ: class J
  let cN: class N
  let cT: class T
  assume uniioombl.1: |- ( ph -> F : NN --> ( <_ i^i ( RR X. RR ) ) )
  assume uniioombl.2: |- ( ph -> Disj_ x e. NN ( (,) ` ( F ` x ) ) )
  assume uniioombl.3: |- S = seq 1 ( + , ( ( abs o. - ) o. F ) )

  disjoint F x
  disjoint ph x
  disjoint a f
  disjoint a i
  disjoint a j
  disjoint a k
  disjoint a n
  disjoint a r
  disjoint a x
  disjoint a y
  disjoint a z
  disjoint F a
  disjoint f i
  disjoint f j
  disjoint f k
  disjoint f n
  disjoint f r
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint F f
  disjoint i j
  disjoint i k
  disjoint i n
  disjoint i r
  disjoint i x
  disjoint i y
  disjoint i z
  disjoint F i
  disjoint j k
  disjoint j n
  disjoint j r
  disjoint j x
  disjoint j y
  disjoint j z
  disjoint F j
  disjoint k n
  disjoint k r
  disjoint k x
  disjoint k y
  disjoint k z
  disjoint F k
  disjoint n r
  disjoint n x
  disjoint n y
  disjoint n z
  disjoint F n
  disjoint r x
  disjoint r y
  disjoint r z
  disjoint F r
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint F y
  disjoint F z
  disjoint a m
  disjoint a w
  disjoint G a
  disjoint i m
  disjoint i w
  disjoint G i
  disjoint j m
  disjoint j w
  disjoint G j
  disjoint k m
  disjoint k w
  disjoint G k
  disjoint m n
  disjoint m w
  disjoint m x
  disjoint m y
  disjoint m z
  disjoint G m
  disjoint n w
  disjoint G n
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint G w
  disjoint G x
  disjoint G y
  disjoint G z
  disjoint K j
  disjoint K n
  disjoint K x
  disjoint K y
  disjoint K z
  disjoint A a
  disjoint A j
  disjoint A k
  disjoint A m
  disjoint A n
  disjoint A x
  disjoint A y
  disjoint A z
  disjoint C a
  disjoint C i
  disjoint C j
  disjoint C k
  disjoint C m
  disjoint C n
  disjoint C x
  disjoint C y
  disjoint C z
  disjoint M i
  disjoint M j
  disjoint M k
  disjoint M n
  disjoint M w
  disjoint M x
  disjoint M y
  disjoint M z
  disjoint E m
  disjoint E n
  disjoint H n
  disjoint H x
  disjoint H y
  disjoint H z
  disjoint J n
  disjoint J x
  disjoint J y
  disjoint J z
  disjoint N i
  disjoint N j
  disjoint N n
  disjoint N z
  disjoint S n
  disjoint S y
  disjoint a ph
  disjoint f m
  disjoint f ph
  disjoint i ph
  disjoint j ph
  disjoint k ph
  disjoint m r
  disjoint m ph
  disjoint n ph
  disjoint ph r
  disjoint ph y
  disjoint ph z
  disjoint T a
  disjoint T i
  disjoint T j
  disjoint T k
  disjoint T m
  disjoint T n
  disjoint T x
  disjoint T y
  disjoint T z
  assert |- ( ph -> ( vol* ` U. ran ( (,) o. F ) ) = sup ( ran S , RR* , < ) )

  proof
    wph
    cioo
    cF
    ccom
    #
    crn
    #
    cuni
    #
    covol
    cfv
    #
    cS
    crn
    #
    cxr
    clt
    csup
    #
    wceq
    #
    @3
    @5
    cle
    wbr
    #
    @5
    @3
    cle
    wbr
    #
    wph
    cn
    cle
    cr
    cr
    cxp
    #
    cin
    #
    cF
    wf
    #
    @2
    @2
    wss
    @7
    uniioombl.1
    @2
    ssid
    @2
    cS
    cF
    uniioombl.3
    ovollb
    sylancl
    wph
    @8
    vy
    cv
    #
    @3
    cle
    wbr
    #
    vy
    @4
    wral
    #
    wph
    @14
    vn
    cv
    #
    cS
    cfv
    #
    @3
    cle
    wbr
    #
    vn
    cn
    wral
    #
    wph
    @17
    vn
    cn
    wph
    @15
    cn
    wcel
    #
    wa
    #
    @16
    vx
    c1
    @15
    cfz
    co
    #
    vx
    cv
    #
    @0
    cfv
    #
    ciun
    #
    covol
    cfv
    #
    @3
    cle
    @20
    @16
    @21
    @23
    cvol
    cfv
    #
    vx
    csu
    #
    @24
    cvol
    cfv
    #
    @25
    @20
    @27
    @15
    caddc
    cabs
    cmin
    ccom
    cF
    ccom
    #
    c1
    cseq
    #
    cfv
    @16
    @20
    @26
    vx
    @29
    c1
    @15
    @20
    @22
    @21
    wcel
    #
    wa
    #
    @22
    @29
    cfv
    #
    @22
    cF
    cfv
    #
    c2nd
    cfv
    #
    @34
    c1st
    cfv
    #
    cmin
    co
    #
    @26
    @20
    @11
    @22
    cn
    wcel
    #
    @33
    @37
    wceq
    @31
    wph
    @11
    @19
    uniioombl.1
    adantr
    #
    @22
    @15
    elfznn
    #
    cF
    @29
    @22
    @29
    eqid
    #
    ovolfsval
    syl2an
    @32
    @26
    @23
    covol
    cfv
    #
    @36
    @35
    cioo
    co
    #
    covol
    cfv
    #
    @37
    @32
    @23
    cvol
    cdm
    #
    wcel
    #
    @26
    @42
    wceq
    @32
    @23
    @43
    @45
    @32
    @23
    @34
    cioo
    cfv
    #
    @43
    @20
    @11
    @38
    @23
    @47
    wceq
    #
    @31
    @39
    @40
    cn
    @10
    @22
    cioo
    cF
    fvco3
    #
    syl2an
    @32
    @47
    @36
    @35
    cop
    #
    cioo
    cfv
    @43
    @32
    @34
    @50
    cioo
    @32
    @34
    @9
    wcel
    @34
    @50
    wceq
    @32
    @10
    @9
    @34
    cle
    @9
    inss2
    #
    @20
    @11
    @38
    @34
    @10
    wcel
    @31
    @39
    @40
    cn
    @10
    @22
    cF
    ffvelrn
    syl2an
    sseldi
    @34
    cr
    cr
    1st2nd2
    syl
    fveq2d
    @36
    @35
    cioo
    df-ov
    syl6eqr
    eqtrd
    #
    @36
    @35
    ioombl
    syl6eqel
    #
    @23
    mblvol
    syl
    @32
    @23
    @43
    covol
    @52
    fveq2d
    @32
    @36
    cr
    wcel
    #
    @35
    cr
    wcel
    #
    @36
    @35
    cle
    wbr
    #
    w3a
    #
    @44
    @37
    wceq
    @20
    @11
    @38
    @57
    @31
    @39
    @40
    cF
    @22
    ovolfcl
    syl2an
    #
    @36
    @35
    ovolioo
    syl
    3eqtrd
    #
    eqtr4d
    @20
    @15
    cn
    c1
    cuz
    cfv
    wph
    @19
    simpr
    nnuz
    syl6eleq
    @32
    @26
    @32
    @26
    @37
    cr
    @59
    @32
    @35
    @36
    @32
    @54
    @55
    @56
    @58
    simp2d
    @32
    @54
    @55
    @56
    @58
    simp1d
    resubcld
    eqeltrd
    #
    recnd
    fsumser
    @15
    cS
    @30
    uniioombl.3
    fveq1i
    syl6reqr
    @20
    @21
    cfn
    wcel
    #
    @46
    @26
    cr
    wcel
    #
    wa
    #
    vx
    @21
    wral
    vx
    @21
    @23
    wdisj
    #
    @28
    @27
    wceq
    @20
    c1
    @15
    fzfid
    #
    @20
    @63
    vx
    @21
    @32
    @46
    @62
    @53
    @60
    jca
    ralrimiva
    @21
    cn
    wss
    #
    @20
    vx
    cn
    @23
    wdisj
    #
    @64
    vx
    @21
    cn
    @40
    ssriv
    #
    wph
    @67
    @19
    wph
    @67
    vx
    cn
    @47
    wdisj
    uniioombl.2
    wph
    vx
    cn
    @23
    @47
    wph
    @11
    @38
    @48
    uniioombl.1
    @49
    sylan
    disjeq2dv
    mpbird
    adantr
    vx
    @21
    cn
    @23
    disjss1
    mpsyl
    @21
    @23
    vx
    volfiniun
    syl3anc
    @20
    @24
    @45
    wcel
    #
    @28
    @25
    wceq
    @20
    @61
    @46
    vx
    @21
    wral
    @69
    @65
    @20
    @46
    vx
    @21
    @53
    ralrimiva
    @21
    @23
    vx
    finiunmbl
    syl2anc
    @24
    mblvol
    syl
    3eqtr2d
    @20
    @24
    @2
    wss
    @2
    cr
    wss
    #
    @25
    @3
    cle
    wbr
    @20
    @24
    vx
    cn
    @23
    ciun
    #
    @2
    @66
    @24
    @71
    wss
    @20
    @68
    vx
    @21
    cn
    @23
    iunss1
    mp1i
    @20
    cn
    cr
    cpw
    #
    @0
    wf
    #
    @0
    cn
    wfn
    @71
    @2
    wceq
    wph
    @73
    @19
    wph
    cxr
    cxr
    cxp
    #
    @72
    cioo
    wf
    cn
    @74
    cF
    wf
    #
    @73
    ioof
    wph
    @11
    @10
    @74
    wss
    @75
    uniioombl.1
    @10
    @9
    @74
    @51
    rexpssxrxp
    sstri
    cn
    @10
    @74
    cF
    fss
    sylancl
    cn
    @74
    @72
    cioo
    cF
    fco
    sylancr
    #
    adantr
    cn
    @72
    @0
    ffn
    vx
    cn
    @0
    fniunfv
    3syl
    sseqtrd
    wph
    @70
    @19
    wph
    @1
    @72
    wss
    #
    @70
    wph
    @73
    @77
    @76
    cn
    @72
    @0
    frn
    syl
    @1
    cr
    sspwuni
    sylib
    #
    adantr
    @24
    @2
    ovolss
    syl2anc
    eqbrtrd
    ralrimiva
    wph
    cn
    cc0
    cpnf
    cico
    co
    #
    cS
    wf
    #
    cS
    cn
    wfn
    @14
    @18
    wb
    wph
    @11
    @80
    uniioombl.1
    cS
    cF
    @29
    @41
    uniioombl.3
    ovolsf
    #
    syl
    cn
    @79
    cS
    ffn
    @13
    @17
    vy
    vn
    cn
    cS
    @12
    @16
    @3
    cle
    breq1
    ralrn
    3syl
    mpbird
    wph
    @4
    cxr
    wss
    #
    @3
    cxr
    wcel
    #
    @8
    @14
    wb
    wph
    @4
    @79
    cxr
    wph
    @11
    @80
    @4
    @79
    wss
    uniioombl.1
    @81
    cn
    @79
    cS
    frn
    3syl
    cc0
    cpnf
    icossxr
    syl6ss
    #
    wph
    @70
    @83
    @78
    @2
    ovolcl
    syl
    #
    vy
    @4
    @3
    supxrleub
    syl2anc
    mpbird
    wph
    @83
    @5
    cxr
    wcel
    #
    @6
    @7
    @8
    wa
    wb
    @85
    wph
    @82
    @86
    @84
    @4
    supxrcl
    syl
    @3
    @5
    xrletri3
    syl2anc
    mpbir2and
end
