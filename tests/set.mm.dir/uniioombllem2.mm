include "cn.mm"
include "wcel.mm"
include "wa.mm"
include "caddc.mm"
include "cabs.mm"
include "cmin.mm"
include "ccom.mm"
include "c1.mm"
include "cseq.mm"
include "crn.mm"
include "cr.mm"
include "clt.mm"
include "csup.mm"
include "covol.mm"
include "cfv.mm"
include "cioo.mm"
include "cin.mm"
include "cli.mm"
include "cv.mm"
include "nnuz.mm"
include "eqid.mm"
include "1zzd.mm"
include "eqidd.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "cpnf.mm"
include "cico.mm"
include "co.mm"
include "cxp.mm"
include "wf.mm"
include "cmpt.mm"
include "uniioombllem2a.mm"
include "wss.mm"
include "inss2.mm"
include "a1i.mm"
include "c1st.mm"
include "c2nd.mm"
include "cop.mm"
include "wceq.mm"
include "ffvelrnda.mm"
include "sseldi.mm"
include "1st2nd2.mm"
include "syl.mm"
include "fveq2d.mm"
include "df-ov.mm"
include "syl6eqr.mm"
include "ioossre.mm"
include "syl6eqss.mm"
include "w3a.mm"
include "ovolfcl.mm"
include "sylan.mm"
include "ovolioo.mm"
include "eqtrd.mm"
include "simp2d.mm"
include "simp1d.mm"
include "resubcld.mm"
include "eqeltrd.mm"
include "ovolsscl.mm"
include "syl3anc.mm"
include "adantr.mm"
include "ioorcl.mm"
include "syl2anc.mm"
include "fmptd.mm"
include "cxr.mm"
include "ioorf.mm"
include "feqmptd.mm"
include "fveq2.mm"
include "fmptco.mm"
include "feq1d.mm"
include "mpbird.mm"
include "ovolfsf.mm"
include "elrege0.mm"
include "sylib.mm"
include "simpld.mm"
include "simprd.mm"
include "wral.mm"
include "wrex.mm"
include "cuni.mm"
include "wdisj.mm"
include "fveq1d.mm"
include "cvv.mm"
include "fvex.mm"
include "fvmpt2.mm"
include "mpan2.mm"
include "sylan9eq.mm"
include "ioorinv.mm"
include "ralrimiva.mm"
include "ineq1d.mm"
include "eqeq12d.mm"
include "rspccva.mm"
include "inss1.mm"
include "disjss2.mm"
include "sylc.mm"
include "uniioovol.mm"
include "ciun.mm"
include "mpteq2dva.mm"
include "rexpssxrxp.mm"
include "sstri.mm"
include "cpw.mm"
include "ioof.mm"
include "3eqtr4d.mm"
include "rneqd.mm"
include "unieqd.mm"
include "inex1.mm"
include "incom.mm"
include "syl6eq.mm"
include "iuneq2i.mm"
include "iunin2.mm"
include "eqtri.mm"
include "wfn.mm"
include "ffn.mm"
include "fniunfv.mm"
include "syl5eqr.mm"
include "fvco3.mm"
include "iuneq2dv.mm"
include "ax-mp.mm"
include "fss.mm"
include "sylancl.mm"
include "fnfco.mm"
include "sylancr.mm"
include "eqtr3d.mm"
include "ineq2d.mm"
include "3eqtr2d.mm"
include "ovolsf.mm"
include "fnfvelrn.mm"
include "frn.mm"
include "icossxr.mm"
include "syl6ss.mm"
include "supxrub.mm"
include "syldan.mm"
include "breq2.mm"
include "ralbidv.mm"
include "rspcev.mm"
include "isumsup2.mm"
include "ovolfs2.mm"
include "coass.mm"
include "coeq2d.mm"
include "syl5eq.mm"
include "seqeq3d.mm"
include "c0.mm"
include "wne.mm"
include "rge0ssre.mm"
include "cdm.mm"
include "1nn.mm"
include "fdm.mm"
include "syl5eleqr.mm"
include "ne0i.mm"
include "dm0rn0.mm"
include "necon3bii.mm"
include "wb.mm"
include "breq1.mm"
include "ralrn.mm"
include "rexbidv.mm"
include "supxrre.mm"
include "3brtr3d.mm"

theorem uniioombllem2
  let wph: wff ph
  let vx: setvar x
  let vz: setvar z
  let cA: class A
  let cC: class C
  let cS: class S
  let cT: class T
  let cE: class E
  let cF: class F
  let cG: class G
  let cH: class H
  let cJ: class J
  let cK: class K
  let va: setvar a
  let vf: setvar f
  let vi: setvar i
  let vj: setvar j
  let vk: setvar k
  let vn: setvar n
  let vr: setvar r
  let vy: setvar y
  let vm: setvar m
  let vw: setvar w
  let cM: class M
  let cN: class N
  assume uniioombl.1: |- ( ph -> F : NN --> ( <_ i^i ( RR X. RR ) ) )
  assume uniioombl.2: |- ( ph -> Disj_ x e. NN ( (,) ` ( F ` x ) ) )
  assume uniioombl.3: |- S = seq 1 ( + , ( ( abs o. - ) o. F ) )
  assume uniioombl.a: |- A = U. ran ( (,) o. F )
  assume uniioombl.e: |- ( ph -> ( vol* ` E ) e. RR )
  assume uniioombl.c: |- ( ph -> C e. RR+ )
  assume uniioombl.g: |- ( ph -> G : NN --> ( <_ i^i ( RR X. RR ) ) )
  assume uniioombl.s: |- ( ph -> E C_ U. ran ( (,) o. G ) )
  assume uniioombl.t: |- T = seq 1 ( + , ( ( abs o. - ) o. G ) )
  assume uniioombl.v: |- ( ph -> sup ( ran T , RR* , < ) <_ ( ( vol* ` E ) + C ) )
  assume uniioombllem2.h: |- H = ( z e. NN |-> ( ( (,) ` ( F ` z ) ) i^i ( (,) ` ( G ` J ) ) ) )
  assume uniioombllem2.k: |- K = ( x e. ran (,) |-> if ( x = (/) , <. 0 , 0 >. , <. inf ( x , RR* , < ) , sup ( x , RR* , < ) >. ) )

  disjoint x z
  disjoint F x
  disjoint F z
  disjoint G x
  disjoint G z
  disjoint K x
  disjoint K z
  disjoint A x
  disjoint A z
  disjoint C x
  disjoint C z
  disjoint H x
  disjoint H z
  disjoint J x
  disjoint J z
  disjoint ph x
  disjoint ph z
  disjoint T x
  disjoint T z
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
  disjoint y z
  disjoint F y
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
  disjoint G y
  disjoint K j
  disjoint K n
  disjoint K y
  disjoint A a
  disjoint A j
  disjoint A k
  disjoint A m
  disjoint A n
  disjoint A y
  disjoint C a
  disjoint C i
  disjoint C j
  disjoint C k
  disjoint C m
  disjoint C n
  disjoint C y
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
  disjoint H y
  disjoint J n
  disjoint J y
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
  disjoint T a
  disjoint T i
  disjoint T j
  disjoint T k
  disjoint T m
  disjoint T n
  disjoint T y
  assert |- ( ( ph /\ J e. NN ) -> seq 1 ( + , ( vol* o. H ) ) ~~> ( vol* ` ( ( (,) ` ( G ` J ) ) i^i A ) ) )

  proof
    wph
    cJ
    cn
    wcel
    #
    wa
    #
    caddc
    cabs
    cmin
    ccom
    cK
    cH
    ccom
    #
    ccom
    #
    c1
    cseq
    #
    @4
    crn
    #
    cr
    clt
    csup
    #
    caddc
    covol
    cH
    ccom
    #
    c1
    cseq
    cJ
    cG
    cfv
    #
    cioo
    cfv
    #
    cA
    cin
    #
    covol
    cfv
    #
    cli
    @1
    vx
    vn
    cv
    #
    @3
    cfv
    #
    vy
    vn
    @3
    @4
    c1
    cn
    nnuz
    @4
    eqid
    #
    @1
    1zzd
    @1
    @12
    cn
    wcel
    wa
    #
    @13
    eqidd
    @15
    @13
    cr
    wcel
    #
    cc0
    @13
    cle
    wbr
    #
    @15
    @13
    cc0
    cpnf
    cico
    co
    #
    wcel
    @16
    @17
    wa
    @1
    cn
    @18
    @12
    @3
    @1
    cn
    cle
    cr
    cr
    cxp
    #
    cin
    #
    @2
    wf
    #
    cn
    @18
    @3
    wf
    @1
    @21
    cn
    @20
    vz
    cn
    vz
    cv
    #
    cF
    cfv
    #
    cioo
    cfv
    #
    @9
    cin
    #
    cK
    cfv
    #
    cmpt
    #
    wf
    @1
    vz
    cn
    @26
    @20
    @27
    @1
    @22
    cn
    wcel
    #
    wa
    #
    @25
    cioo
    crn
    #
    wcel
    #
    @25
    covol
    cfv
    cr
    wcel
    #
    @26
    @20
    wcel
    wph
    vx
    vz
    cA
    cC
    cS
    cT
    cE
    cF
    cG
    cJ
    uniioombl.1
    uniioombl.2
    uniioombl.3
    uniioombl.a
    uniioombl.e
    uniioombl.c
    uniioombl.g
    uniioombl.s
    uniioombl.t
    uniioombl.v
    uniioombllem2a
    #
    @1
    @32
    @28
    @1
    @25
    @9
    wss
    #
    @9
    cr
    wss
    #
    @9
    covol
    cfv
    #
    cr
    wcel
    #
    @32
    @34
    @1
    @24
    @9
    inss2
    a1i
    @1
    @9
    @8
    c1st
    cfv
    #
    @8
    c2nd
    cfv
    #
    cioo
    co
    #
    cr
    @1
    @9
    @38
    @39
    cop
    #
    cioo
    cfv
    @40
    @1
    @8
    @41
    cioo
    @1
    @8
    @19
    wcel
    @8
    @41
    wceq
    @1
    @20
    @19
    @8
    cle
    @19
    inss2
    #
    wph
    cn
    @20
    cJ
    cG
    uniioombl.g
    ffvelrnda
    sseldi
    @8
    cr
    cr
    1st2nd2
    syl
    fveq2d
    @38
    @39
    cioo
    df-ov
    syl6eqr
    #
    @38
    @39
    ioossre
    syl6eqss
    #
    @1
    @36
    @39
    @38
    cmin
    co
    #
    cr
    @1
    @36
    @40
    covol
    cfv
    #
    @45
    @1
    @9
    @40
    covol
    @43
    fveq2d
    @1
    @38
    cr
    wcel
    #
    @39
    cr
    wcel
    #
    @38
    @39
    cle
    wbr
    #
    w3a
    #
    @46
    @45
    wceq
    wph
    cn
    @20
    cG
    wf
    @0
    @50
    uniioombl.g
    cG
    cJ
    ovolfcl
    sylan
    #
    @38
    @39
    ovolioo
    syl
    eqtrd
    @1
    @39
    @38
    @1
    @47
    @48
    @49
    @51
    simp2d
    @1
    @47
    @48
    @49
    @51
    simp1d
    resubcld
    eqeltrd
    #
    @25
    @9
    ovolsscl
    syl3anc
    adantr
    vx
    @25
    cK
    uniioombllem2.k
    ioorcl
    syl2anc
    #
    @27
    eqid
    #
    fmptd
    @1
    cn
    @20
    @2
    @27
    @1
    vz
    vy
    cn
    @30
    @25
    vy
    cv
    #
    cK
    cfv
    @26
    cH
    cK
    @33
    cH
    vz
    cn
    @25
    cmpt
    #
    wceq
    @1
    uniioombllem2.h
    a1i
    #
    @1
    vy
    @30
    cle
    cxr
    cxr
    cxp
    #
    cin
    #
    cK
    @30
    @59
    cK
    wf
    @1
    vx
    cK
    uniioombllem2.k
    ioorf
    a1i
    feqmptd
    @55
    @25
    cK
    fveq2
    fmptco
    #
    feq1d
    mpbird
    #
    @2
    @3
    @3
    eqid
    #
    ovolfsf
    syl
    ffvelrnda
    @13
    elrege0
    sylib
    #
    simpld
    @15
    @16
    @17
    @63
    simprd
    @1
    @5
    cxr
    clt
    csup
    #
    cr
    wcel
    @55
    @4
    cfv
    #
    @64
    cle
    wbr
    #
    vy
    cn
    wral
    #
    @65
    vx
    cv
    #
    cle
    wbr
    #
    vy
    cn
    wral
    #
    vx
    cr
    wrex
    #
    @1
    @64
    @11
    cr
    @1
    cioo
    @2
    ccom
    #
    crn
    #
    cuni
    #
    covol
    cfv
    @64
    @11
    @1
    vx
    @4
    @2
    @61
    @1
    @68
    @2
    cfv
    #
    cioo
    cfv
    #
    @68
    cF
    cfv
    #
    cioo
    cfv
    #
    wss
    #
    vx
    cn
    wral
    vx
    cn
    @78
    wdisj
    #
    vx
    cn
    @76
    wdisj
    @1
    @79
    vx
    cn
    @1
    @68
    cn
    wcel
    #
    wa
    @76
    @78
    @9
    cin
    #
    @78
    @1
    @22
    @2
    cfv
    #
    cioo
    cfv
    #
    @25
    wceq
    #
    vz
    cn
    wral
    @81
    @76
    @82
    wceq
    #
    @1
    @85
    vz
    cn
    @29
    @84
    @26
    cioo
    cfv
    #
    @25
    @29
    @83
    @26
    cioo
    @1
    @28
    @83
    @22
    @27
    cfv
    #
    @26
    @1
    @22
    @2
    @27
    @60
    fveq1d
    @28
    @26
    cvv
    wcel
    @88
    @26
    wceq
    @25
    cK
    fvex
    vz
    cn
    @26
    cvv
    @27
    @54
    fvmpt2
    mpan2
    sylan9eq
    fveq2d
    @29
    @31
    @87
    @25
    wceq
    @33
    vx
    @25
    cK
    uniioombllem2.k
    ioorinv
    syl
    #
    eqtrd
    ralrimiva
    @85
    @86
    vz
    @68
    cn
    @22
    @68
    wceq
    #
    @84
    @76
    @25
    @82
    @90
    @83
    @75
    cioo
    @22
    @68
    @2
    fveq2
    fveq2d
    @90
    @24
    @78
    @9
    @90
    @23
    @77
    cioo
    @22
    @68
    cF
    fveq2
    fveq2d
    ineq1d
    eqeq12d
    rspccva
    sylan
    @78
    @9
    inss1
    syl6eqss
    ralrimiva
    wph
    @80
    @0
    uniioombl.2
    adantr
    vx
    cn
    @76
    @78
    disjss2
    sylc
    @14
    uniioovol
    @1
    @74
    @10
    covol
    @1
    @74
    cH
    crn
    #
    cuni
    #
    @9
    vz
    cn
    @24
    ciun
    #
    cin
    #
    @10
    @1
    @73
    @91
    @1
    @72
    cH
    @1
    vz
    cn
    @87
    cmpt
    @56
    @72
    cH
    @1
    vz
    cn
    @87
    @25
    @89
    mpteq2dva
    @1
    vz
    vy
    cn
    @58
    @26
    @55
    cioo
    cfv
    @87
    @2
    cioo
    @29
    @20
    @58
    @26
    @20
    @19
    @58
    @42
    rexpssxrxp
    sstri
    #
    @53
    sseldi
    @60
    @1
    vy
    @58
    cr
    cpw
    #
    cioo
    @58
    @96
    cioo
    wf
    #
    @1
    ioof
    a1i
    feqmptd
    @55
    @26
    cioo
    fveq2
    fmptco
    @57
    3eqtr4d
    #
    rneqd
    unieqd
    @1
    @94
    vz
    cn
    @22
    cH
    cfv
    #
    ciun
    #
    @92
    @100
    vz
    cn
    @9
    @24
    cin
    #
    ciun
    @94
    vz
    cn
    @99
    @101
    @28
    @99
    @25
    @101
    @28
    @25
    cvv
    wcel
    @99
    @25
    wceq
    @24
    @9
    @23
    cioo
    fvex
    inex1
    vz
    cn
    @25
    cvv
    cH
    uniioombllem2.h
    fvmpt2
    mpan2
    @24
    @9
    incom
    syl6eq
    iuneq2i
    vz
    cn
    @9
    @24
    iunin2
    eqtri
    @1
    cH
    cn
    wfn
    #
    @100
    @92
    wceq
    @1
    cn
    @30
    cH
    wf
    @102
    @1
    vz
    cn
    @25
    @30
    cH
    @33
    uniioombllem2.h
    fmptd
    cn
    @30
    cH
    ffn
    syl
    vz
    cn
    cH
    fniunfv
    syl
    syl5eqr
    @1
    @93
    cA
    @9
    @1
    vz
    cn
    @22
    cioo
    cF
    ccom
    #
    cfv
    #
    ciun
    #
    @93
    cA
    @1
    vz
    cn
    @104
    @24
    @1
    cn
    @20
    cF
    wf
    #
    @28
    @104
    @24
    wceq
    wph
    @106
    @0
    uniioombl.1
    adantr
    #
    cn
    @20
    @22
    cioo
    cF
    fvco3
    sylan
    iuneq2dv
    @1
    @105
    @103
    crn
    cuni
    #
    cA
    @1
    @103
    cn
    wfn
    #
    @105
    @108
    wceq
    @1
    cioo
    @58
    wfn
    #
    cn
    @58
    cF
    wf
    #
    @109
    @97
    @110
    ioof
    @58
    @96
    cioo
    ffn
    ax-mp
    @1
    @106
    @20
    @58
    wss
    @111
    @107
    @95
    cn
    @20
    @58
    cF
    fss
    sylancl
    @58
    cn
    cioo
    cF
    fnfco
    sylancr
    vz
    cn
    @103
    fniunfv
    syl
    uniioombl.a
    syl6eqr
    eqtr3d
    ineq2d
    3eqtr2d
    fveq2d
    eqtr3d
    #
    @1
    @10
    @9
    wss
    #
    @35
    @37
    @11
    cr
    wcel
    @113
    @1
    @9
    cA
    inss1
    a1i
    @44
    @52
    @10
    @9
    ovolsscl
    syl3anc
    eqeltrd
    @1
    @66
    vy
    cn
    @1
    @55
    cn
    wcel
    #
    @65
    @5
    wcel
    #
    @66
    @1
    @4
    cn
    wfn
    #
    @114
    @115
    @1
    cn
    @18
    @4
    wf
    #
    @116
    @1
    @21
    @117
    @61
    @4
    @2
    @3
    @62
    @14
    ovolsf
    syl
    #
    cn
    @18
    @4
    ffn
    syl
    #
    cn
    @55
    @4
    fnfvelrn
    sylan
    @1
    @5
    cxr
    wss
    @115
    @66
    @1
    @5
    @18
    cxr
    @1
    @117
    @5
    @18
    wss
    @118
    cn
    @18
    @4
    frn
    syl
    #
    cc0
    cpnf
    icossxr
    syl6ss
    @5
    @65
    supxrub
    sylan
    syldan
    ralrimiva
    @70
    @67
    vx
    @64
    cr
    @68
    @64
    wceq
    @69
    @66
    vy
    cn
    @68
    @64
    @65
    cle
    breq2
    ralbidv
    rspcev
    syl2anc
    #
    isumsup2
    @1
    @3
    @7
    caddc
    c1
    @1
    @3
    covol
    cioo
    ccom
    @2
    ccom
    #
    @7
    @1
    @21
    @3
    @122
    wceq
    @61
    @2
    @3
    @62
    ovolfs2
    syl
    @1
    @122
    covol
    @72
    ccom
    @7
    covol
    cioo
    @2
    coass
    @1
    @72
    cH
    covol
    @98
    coeq2d
    syl5eq
    eqtrd
    seqeq3d
    @1
    @64
    @6
    @11
    @1
    @5
    cr
    wss
    @5
    c0
    wne
    #
    @22
    @68
    cle
    wbr
    #
    vz
    @5
    wral
    #
    vx
    cr
    wrex
    #
    @64
    @6
    wceq
    @1
    @5
    @18
    cr
    @120
    rge0ssre
    syl6ss
    @1
    @4
    cdm
    #
    c0
    wne
    #
    @123
    @1
    c1
    @127
    wcel
    @128
    @1
    c1
    cn
    @127
    1nn
    @1
    @117
    @127
    cn
    wceq
    @118
    cn
    @18
    @4
    fdm
    syl
    syl5eleqr
    @127
    c1
    ne0i
    syl
    @127
    c0
    @5
    c0
    @4
    dm0rn0
    necon3bii
    sylib
    @1
    @126
    @71
    @121
    @1
    @125
    @70
    vx
    cr
    @1
    @116
    @125
    @70
    wb
    @119
    @124
    @69
    vz
    vy
    cn
    @4
    @22
    @65
    @68
    cle
    breq1
    ralrn
    syl
    rexbidv
    mpbird
    vx
    vz
    @5
    supxrre
    syl3anc
    @112
    eqtr3d
    3brtr3d
end
