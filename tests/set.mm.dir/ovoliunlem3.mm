include "cn.mm"
include "ciun.mm"
include "covol.mm"
include "cfv.mm"
include "cv.mm"
include "csb.mm"
include "crn.mm"
include "cxr.mm"
include "clt.mm"
include "csup.mm"
include "caddc.mm"
include "co.mm"
include "cle.mm"
include "nfcv.mm"
include "nfcsb1v.mm"
include "csbeq1a.mm"
include "cbviun.mm"
include "fveq2i.mm"
include "cr.mm"
include "cxp.mm"
include "cin.mm"
include "cmap.mm"
include "wf.mm"
include "cioo.mm"
include "ccom.mm"
include "cuni.mm"
include "wss.mm"
include "cabs.mm"
include "cmin.mm"
include "c1.mm"
include "cseq.mm"
include "c2.mm"
include "cexp.mm"
include "cdiv.mm"
include "wbr.mm"
include "wa.mm"
include "wral.mm"
include "wex.mm"
include "wrex.mm"
include "wcel.mm"
include "crp.mm"
include "cn0.mm"
include "2nn.mm"
include "nnnn0.mm"
include "nnexpcl.mm"
include "sylancr.mm"
include "nnrpd.mm"
include "rpdivcl.mm"
include "syl2an.mm"
include "eqid.mm"
include "ovolgelb.mm"
include "syl3anc.mm"
include "ralrimiva.mm"
include "ovex.mm"
include "nnenom.mm"
include "wceq.mm"
include "coeq2.mm"
include "rneqd.mm"
include "unieqd.mm"
include "sseq2d.mm"
include "seqeq3d.mm"
include "supeq1d.mm"
include "breq1d.mm"
include "anbi12d.mm"
include "axcc4.mm"
include "syl.mm"
include "wf1o.mm"
include "wi.mm"
include "cen.mm"
include "xpnnen.mm"
include "ensymi.mm"
include "bren.mm"
include "mpbi.mm"
include "c2nd.mm"
include "c1st.mm"
include "cmpt.mm"
include "nffv.mm"
include "fveq2d.mm"
include "cbvmpt.mm"
include "eqtri.mm"
include "simpll.mm"
include "nfv.mm"
include "nfss.mm"
include "sseq1d.mm"
include "cbvral.mm"
include "sylib.mm"
include "r19.21bi.mm"
include "sylan.mm"
include "nfel1.mm"
include "eleq1d.mm"
include "ad2antrr.mm"
include "simplr.mm"
include "simprl.mm"
include "simprr.mm"
include "nfov.mm"
include "nfbr.mm"
include "nfan.mm"
include "fveq2.mm"
include "coeq2d.mm"
include "sseq12d.mm"
include "oveq2.mm"
include "oveq2d.mm"
include "oveq12d.mm"
include "breq12d.mm"
include "simpld.mm"
include "simprd.mm"
include "ovoliunlem2.mm"
include "exp31.mm"
include "exlimdv.mm"
include "mpi.mm"
include "mpd.mm"
include "syl5eqbr.mm"

theorem ovoliunlem3
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cT: class T
  let vn: setvar n
  let cG: class G
  let vf: setvar f
  let vg: setvar g
  let vj: setvar j
  let vk: setvar k
  let vm: setvar m
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vi: setvar i
  let cF: class F
  let vw: setvar w
  let cJ: class J
  let cK: class K
  let cL: class L
  let cH: class H
  let cS: class S
  let cU: class U
  assume ovoliun.t: |- T = seq 1 ( + , G )
  assume ovoliun.g: |- G = ( n e. NN |-> ( vol* ` A ) )
  assume ovoliun.a: |- ( ( ph /\ n e. NN ) -> A C_ RR )
  assume ovoliun.v: |- ( ( ph /\ n e. NN ) -> ( vol* ` A ) e. RR )
  assume ovoliun.r: |- ( ph -> sup ( ran T , RR* , < ) e. RR )
  assume ovoliun.b: |- ( ph -> B e. RR+ )

  disjoint G n
  disjoint T n
  disjoint B n
  disjoint n ph
  disjoint f g
  disjoint f j
  disjoint f k
  disjoint f m
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint A f
  disjoint g j
  disjoint g k
  disjoint g m
  disjoint g x
  disjoint g y
  disjoint g z
  disjoint A g
  disjoint j k
  disjoint j m
  disjoint j x
  disjoint j y
  disjoint j z
  disjoint A j
  disjoint k m
  disjoint k x
  disjoint k y
  disjoint k z
  disjoint A k
  disjoint m x
  disjoint m y
  disjoint m z
  disjoint A m
  disjoint x y
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint f n
  disjoint B f
  disjoint g n
  disjoint B g
  disjoint j n
  disjoint B j
  disjoint k n
  disjoint B k
  disjoint m n
  disjoint B m
  disjoint n x
  disjoint n y
  disjoint n z
  disjoint B x
  disjoint B y
  disjoint B z
  disjoint f i
  disjoint F f
  disjoint i j
  disjoint i k
  disjoint i m
  disjoint i n
  disjoint i x
  disjoint i z
  disjoint F i
  disjoint F j
  disjoint F k
  disjoint F m
  disjoint F n
  disjoint F x
  disjoint F z
  disjoint i w
  disjoint i y
  disjoint J i
  disjoint j w
  disjoint J j
  disjoint k w
  disjoint J k
  disjoint m w
  disjoint J m
  disjoint n w
  disjoint J n
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint J w
  disjoint J x
  disjoint J y
  disjoint J z
  disjoint K i
  disjoint K j
  disjoint K m
  disjoint K n
  disjoint K w
  disjoint K x
  disjoint K y
  disjoint K z
  disjoint L i
  disjoint L j
  disjoint L k
  disjoint L n
  disjoint L w
  disjoint L x
  disjoint L y
  disjoint L z
  disjoint H f
  disjoint H j
  disjoint H m
  disjoint H n
  disjoint H z
  disjoint g i
  disjoint g ph
  disjoint i ph
  disjoint j ph
  disjoint k ph
  disjoint m ph
  disjoint ph x
  disjoint ph y
  disjoint ph z
  disjoint S f
  disjoint S k
  disjoint S x
  disjoint S y
  disjoint S z
  disjoint G k
  disjoint G m
  disjoint G x
  disjoint T g
  disjoint T j
  disjoint T k
  disjoint T m
  disjoint T x
  disjoint T y
  disjoint T z
  disjoint U f
  disjoint U j
  disjoint U x
  disjoint U y
  disjoint U z
  assert |- ( ph -> ( vol* ` U_ n e. NN A ) <_ ( sup ( ran T , RR* , < ) + B ) )

  proof
    wph
    vn
    cn
    cA
    ciun
    #
    covol
    cfv
    vm
    cn
    vn
    vm
    cv
    #
    cA
    csb
    #
    ciun
    #
    covol
    cfv
    #
    cT
    crn
    cxr
    clt
    csup
    #
    cB
    caddc
    co
    #
    cle
    @0
    @3
    covol
    vn
    vm
    cn
    cA
    @2
    vm
    cA
    nfcv
    vn
    @1
    cA
    nfcsb1v
    #
    vn
    @1
    cA
    csbeq1a
    #
    cbviun
    fveq2i
    wph
    cn
    cle
    cr
    cr
    cxp
    cin
    #
    cn
    cmap
    co
    #
    vg
    cv
    #
    wf
    #
    cA
    cioo
    vn
    cv
    #
    @11
    cfv
    #
    ccom
    #
    crn
    #
    cuni
    #
    wss
    #
    caddc
    cabs
    cmin
    ccom
    #
    @14
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
    cA
    covol
    cfv
    #
    cB
    c2
    @13
    cexp
    co
    #
    cdiv
    co
    #
    caddc
    co
    #
    cle
    wbr
    #
    wa
    #
    vn
    cn
    wral
    #
    wa
    #
    vg
    wex
    #
    @4
    @6
    cle
    wbr
    #
    wph
    cA
    cioo
    vf
    cv
    #
    ccom
    #
    crn
    #
    cuni
    #
    wss
    #
    caddc
    @19
    @34
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
    @27
    cle
    wbr
    #
    wa
    #
    vf
    @10
    wrex
    #
    vn
    cn
    wral
    @32
    wph
    @45
    vn
    cn
    wph
    @13
    cn
    wcel
    #
    wa
    cA
    cr
    wss
    #
    @24
    cr
    wcel
    #
    @26
    crp
    wcel
    #
    @45
    ovoliun.a
    ovoliun.v
    wph
    cB
    crp
    wcel
    #
    @25
    crp
    wcel
    @49
    @46
    ovoliun.b
    @46
    @25
    @46
    c2
    cn
    wcel
    @13
    cn0
    wcel
    @25
    cn
    wcel
    2nn
    @13
    nnnn0
    c2
    @13
    nnexpcl
    sylancr
    nnrpd
    cB
    @25
    rpdivcl
    syl2an
    cA
    @26
    @40
    vf
    @40
    eqid
    ovolgelb
    syl3anc
    ralrimiva
    @44
    @29
    vf
    @10
    vg
    vn
    cn
    @9
    cn
    cmap
    ovex
    nnenom
    @34
    @14
    wceq
    #
    @38
    @18
    @43
    @28
    @51
    @37
    @17
    cA
    @51
    @36
    @16
    @51
    @35
    @15
    @34
    @14
    cioo
    coeq2
    rneqd
    unieqd
    sseq2d
    @51
    @42
    @23
    @27
    cle
    @51
    cxr
    @41
    @22
    clt
    @51
    @40
    @21
    @51
    @39
    @20
    caddc
    c1
    @34
    @14
    @19
    coeq2
    seqeq3d
    rneqd
    supeq1d
    breq1d
    anbi12d
    axcc4
    syl
    wph
    @31
    @33
    vg
    wph
    cn
    cn
    cn
    cxp
    #
    vj
    cv
    #
    wf1o
    #
    vj
    wex
    #
    @31
    @33
    wi
    #
    cn
    @52
    cen
    wbr
    @55
    @52
    cn
    xpnnen
    ensymi
    cn
    @52
    vj
    bren
    mpbi
    wph
    @54
    @56
    vj
    wph
    @54
    @31
    @33
    wph
    @54
    wa
    #
    @31
    wa
    #
    @2
    cB
    caddc
    @19
    @1
    @11
    cfv
    #
    ccom
    #
    c1
    cseq
    #
    cT
    caddc
    @19
    vk
    cn
    vk
    cv
    @53
    cfv
    #
    c2nd
    cfv
    @62
    c1st
    cfv
    @11
    cfv
    cfv
    cmpt
    #
    ccom
    c1
    cseq
    #
    vk
    vm
    @11
    cG
    @63
    @53
    ovoliun.t
    cG
    vn
    cn
    @24
    cmpt
    vm
    cn
    @2
    covol
    cfv
    #
    cmpt
    ovoliun.g
    vn
    vm
    cn
    @24
    @65
    vm
    @24
    nfcv
    #
    vn
    @2
    covol
    vn
    covol
    nfcv
    @7
    nffv
    #
    @13
    @1
    wceq
    #
    cA
    @2
    covol
    @8
    fveq2d
    #
    cbvmpt
    eqtri
    @58
    wph
    @1
    cn
    wcel
    #
    @2
    cr
    wss
    #
    wph
    @54
    @31
    simpll
    #
    wph
    @71
    vm
    cn
    wph
    @47
    vn
    cn
    wral
    @71
    vm
    cn
    wral
    wph
    @47
    vn
    cn
    ovoliun.a
    ralrimiva
    @47
    @71
    vn
    vm
    cn
    @47
    vm
    nfv
    vn
    @2
    cr
    @7
    vn
    cr
    nfcv
    nfss
    @68
    cA
    @2
    cr
    @8
    sseq1d
    cbvral
    sylib
    r19.21bi
    sylan
    @58
    wph
    @70
    @65
    cr
    wcel
    #
    @72
    wph
    @73
    vm
    cn
    wph
    @48
    vn
    cn
    wral
    @73
    vm
    cn
    wral
    wph
    @48
    vn
    cn
    ovoliun.v
    ralrimiva
    @48
    @73
    vn
    vm
    cn
    vm
    @24
    cr
    @66
    nfel1
    vn
    @65
    cr
    @67
    nfel1
    @68
    @24
    @65
    cr
    @69
    eleq1d
    cbvral
    sylib
    r19.21bi
    sylan
    wph
    @5
    cr
    wcel
    @54
    @31
    ovoliun.r
    ad2antrr
    wph
    @50
    @54
    @31
    ovoliun.b
    ad2antrr
    @61
    eqid
    @64
    eqid
    @63
    eqid
    wph
    @54
    @31
    simplr
    @57
    @12
    @30
    simprl
    @58
    @70
    wa
    #
    @2
    cioo
    @59
    ccom
    #
    crn
    #
    cuni
    #
    wss
    #
    @61
    crn
    #
    cxr
    clt
    csup
    #
    @65
    cB
    c2
    @1
    cexp
    co
    #
    cdiv
    co
    #
    caddc
    co
    #
    cle
    wbr
    #
    @58
    @78
    @84
    wa
    #
    vm
    cn
    @58
    @30
    @85
    vm
    cn
    wral
    @57
    @12
    @30
    simprr
    @29
    @85
    vn
    vm
    cn
    @29
    vm
    nfv
    @78
    @84
    vn
    vn
    @2
    @77
    @7
    vn
    @77
    nfcv
    nfss
    vn
    @80
    @83
    cle
    vn
    @80
    nfcv
    vn
    cle
    nfcv
    vn
    @65
    @82
    caddc
    @67
    vn
    caddc
    nfcv
    vn
    @82
    nfcv
    nfov
    nfbr
    nfan
    @68
    @18
    @78
    @28
    @84
    @68
    cA
    @2
    @17
    @77
    @8
    @68
    @16
    @76
    @68
    @15
    @75
    @68
    @14
    @59
    cioo
    @13
    @1
    @11
    fveq2
    #
    coeq2d
    rneqd
    unieqd
    sseq12d
    @68
    @23
    @80
    @27
    @83
    cle
    @68
    cxr
    @22
    @79
    clt
    @68
    @21
    @61
    @68
    @20
    @60
    caddc
    c1
    @68
    @14
    @59
    @19
    @86
    coeq2d
    seqeq3d
    rneqd
    supeq1d
    @68
    @24
    @65
    @26
    @82
    caddc
    @69
    @68
    @25
    @81
    cB
    cdiv
    @13
    @1
    c2
    cexp
    oveq2
    oveq2d
    oveq12d
    breq12d
    anbi12d
    cbvral
    sylib
    r19.21bi
    #
    simpld
    @74
    @78
    @84
    @87
    simprd
    ovoliunlem2
    exp31
    exlimdv
    mpi
    exlimdv
    mpd
    syl5eqbr
end
