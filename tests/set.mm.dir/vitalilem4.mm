include "cv.mm"
include "cn.mm"
include "wcel.mm"
include "wa.mm"
include "cfv.mm"
include "covol.mm"
include "crn.mm"
include "cc0.mm"
include "cmin.mm"
include "co.mm"
include "cr.mm"
include "crab.mm"
include "wceq.mm"
include "fveq2.mm"
include "oveq2d.mm"
include "eleq1d.mm"
include "rabbidv.mm"
include "reex.mm"
include "rabex.mm"
include "fvmpt.mm"
include "adantl.mm"
include "fveq2d.mm"
include "wss.mm"
include "c1.mm"
include "cicc.mm"
include "ciun.mm"
include "cneg.mm"
include "c2.mm"
include "vitalilem2.mm"
include "simp1d.mm"
include "unitssre.mm"
include "syl6ss.mm"
include "adantr.mm"
include "neg1rr.mm"
include "1re.mm"
include "iccssre.mm"
include "mp2an.mm"
include "cq.mm"
include "cin.mm"
include "inss2.mm"
include "wf1o.mm"
include "wf.mm"
include "f1of.mm"
include "syl.mm"
include "ffvelrnda.mm"
include "sseldi.mm"
include "eqidd.mm"
include "ovolshft.mm"
include "eqtr4d.mm"
include "clt.mm"
include "wbr.mm"
include "wn.mm"
include "c3.mm"
include "cdiv.mm"
include "cfl.mm"
include "caddc.mm"
include "cmul.mm"
include "cxr.mm"
include "3re.mm"
include "rexri.mm"
include "a1i.mm"
include "cn0.mm"
include "cle.mm"
include "crp.mm"
include "3nn.mm"
include "nnrp.mm"
include "ax-mp.mm"
include "0re.mm"
include "0le1.mm"
include "ovolicc.mm"
include "mp3an.mm"
include "1m0e1.mm"
include "eqtri.mm"
include "eqeltri.mm"
include "ovolsscl.mm"
include "mp3an23.mm"
include "simpr.mm"
include "elrpd.mm"
include "rpdivcl.mm"
include "sylancr.mm"
include "rpred.mm"
include "rpge0d.mm"
include "flge0nn0.mm"
include "syl2anc.mm"
include "nn0p1nn.mm"
include "nnred.mm"
include "remulcld.mm"
include "rexrd.mm"
include "cvol.mm"
include "cdm.mm"
include "wral.mm"
include "cpw.mm"
include "cdif.mm"
include "elpw2.mm"
include "sylibr.mm"
include "anim1i.mm"
include "eldif.mm"
include "ex.mm"
include "mt3d.mm"
include "inss1.mm"
include "qssre.mm"
include "sstri.mm"
include "fss.mm"
include "sylancl.mm"
include "shftmbl.mm"
include "fmptd.mm"
include "ralrimiva.mm"
include "iunmbl.mm"
include "mblss.mm"
include "ovolcl.mm"
include "3syl.mm"
include "flltp1.mm"
include "ltdivmul2d.mm"
include "mpbid.mm"
include "cmpt.mm"
include "cseq.mm"
include "csup.mm"
include "nnuz.mm"
include "1zzd.mm"
include "mblvol.mm"
include "eqtrd.mm"
include "eqeltrd.mm"
include "adantlr.mm"
include "eqid.mm"
include "serfre.mm"
include "frn.mm"
include "ressxr.mm"
include "csn.mm"
include "cxp.mm"
include "mpteq2dva.mm"
include "fconstmpt.mm"
include "syl6eqr.mm"
include "seqeq3d.mm"
include "fveq1d.mm"
include "cc.mm"
include "recnd.mm"
include "ser1const.mm"
include "wfn.mm"
include "ffn.mm"
include "fnfvelrn.mm"
include "eqeltrrd.mm"
include "supxrub.mm"
include "wdisj.mm"
include "jca.mm"
include "vitalilem3.mm"
include "voliun.mm"
include "eqtr3d.mm"
include "breqtrrd.mm"
include "xrltletrd.mm"
include "simp3d.mm"
include "2re.mm"
include "ovolss.mm"
include "2cn.mm"
include "ax-1cn.mm"
include "subnegi.mm"
include "neg1lt0.mm"
include "2pos.mm"
include "lttri.mm"
include "ltleii.mm"
include "df-3.mm"
include "3eqtr4i.mm"
include "syl6breq.mm"
include "wb.mm"
include "xrlenlt.mm"
include "pm2.65da.mm"
include "wo.mm"
include "ovolge0.mm"
include "0xr.mm"
include "xrleloe.mm"
include "ord.mm"
include "mpd.mm"

theorem vitalilem4
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let c.sm: class .~
  let cS: class S
  let cT: class T
  let vm: setvar m
  let vn: setvar n
  let cF: class F
  let cG: class G
  let vs: setvar s
  let vk: setvar k
  let vv: setvar v
  let vw: setvar w
  let vu: setvar u
  assume vitali.1: |- .~ = { <. x , y >. | ( ( x e. ( 0 [,] 1 ) /\ y e. ( 0 [,] 1 ) ) /\ ( x - y ) e. QQ ) }
  assume vitali.2: |- S = ( ( 0 [,] 1 ) /. .~ )
  assume vitali.3: |- ( ph -> F Fn S )
  assume vitali.4: |- ( ph -> A. z e. S ( z =/= (/) -> ( F ` z ) e. z ) )
  assume vitali.5: |- ( ph -> G : NN -1-1-onto-> ( QQ i^i ( -u 1 [,] 1 ) ) )
  assume vitali.6: |- T = ( n e. NN |-> { s e. RR | ( s - ( G ` n ) ) e. ran F } )
  assume vitali.7: |- ( ph -> -. ran F e. ( ~P RR \ dom vol ) )

  disjoint m n
  disjoint m s
  disjoint m x
  disjoint m y
  disjoint m z
  disjoint G m
  disjoint n s
  disjoint n x
  disjoint n y
  disjoint n z
  disjoint G n
  disjoint s x
  disjoint s y
  disjoint s z
  disjoint G s
  disjoint x y
  disjoint x z
  disjoint G x
  disjoint y z
  disjoint G y
  disjoint G z
  disjoint m ph
  disjoint n ph
  disjoint ph x
  disjoint ph z
  disjoint S z
  disjoint T m
  disjoint T x
  disjoint F m
  disjoint F n
  disjoint F s
  disjoint F x
  disjoint F y
  disjoint F z
  disjoint .~ m
  disjoint .~ n
  disjoint .~ s
  disjoint .~ x
  disjoint .~ y
  disjoint .~ z
  disjoint k m
  disjoint k n
  disjoint k v
  disjoint k w
  disjoint k x
  disjoint k z
  disjoint k ph
  disjoint m v
  disjoint m w
  disjoint n v
  disjoint n w
  disjoint v w
  disjoint v x
  disjoint v z
  disjoint ph v
  disjoint w x
  disjoint w z
  disjoint ph w
  disjoint S w
  disjoint T k
  disjoint T v
  disjoint T w
  disjoint k s
  disjoint k y
  disjoint F k
  disjoint s v
  disjoint s w
  disjoint v y
  disjoint F v
  disjoint w y
  disjoint F w
  disjoint m u
  disjoint n u
  disjoint s u
  disjoint u v
  disjoint u w
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint .~ u
  disjoint .~ v
  disjoint .~ w
  assert |- ( ( ph /\ m e. NN ) -> ( vol* ` ( T ` m ) ) = 0 )

  proof
    wph
    vm
    cv
    #
    cn
    wcel
    #
    wa
    #
    @0
    cT
    cfv
    #
    covol
    cfv
    #
    cF
    crn
    #
    covol
    cfv
    #
    cc0
    @2
    @4
    vs
    cv
    #
    @0
    cG
    cfv
    #
    cmin
    co
    #
    @5
    wcel
    #
    vs
    cr
    crab
    #
    covol
    cfv
    @6
    @2
    @3
    @11
    covol
    @1
    @3
    @11
    wceq
    wph
    vn
    @0
    @7
    vn
    cv
    #
    cG
    cfv
    #
    cmin
    co
    #
    @5
    wcel
    #
    vs
    cr
    crab
    #
    @11
    cn
    cT
    @12
    @0
    wceq
    #
    @15
    @10
    vs
    cr
    @17
    @14
    @9
    @5
    @17
    @13
    @8
    @7
    cmin
    @12
    @0
    cG
    fveq2
    oveq2d
    eleq1d
    rabbidv
    vitali.6
    @10
    vs
    cr
    reex
    rabex
    fvmpt
    adantl
    fveq2d
    @2
    vs
    @5
    @11
    @8
    wph
    @5
    cr
    wss
    #
    @1
    wph
    @5
    cc0
    c1
    cicc
    co
    #
    cr
    wph
    @5
    @19
    wss
    #
    @19
    vm
    cn
    @3
    ciun
    #
    wss
    #
    @21
    c1
    cneg
    #
    c2
    cicc
    co
    #
    wss
    #
    wph
    vx
    vy
    vz
    c.sm
    cS
    cT
    vm
    vn
    cF
    cG
    vs
    vitali.1
    vitali.2
    vitali.3
    vitali.4
    vitali.5
    vitali.6
    vitali.7
    vitalilem2
    #
    simp1d
    #
    unitssre
    syl6ss
    #
    adantr
    @2
    @23
    c1
    cicc
    co
    #
    cr
    @8
    @23
    cr
    wcel
    #
    c1
    cr
    wcel
    #
    @29
    cr
    wss
    neg1rr
    1re
    @23
    c1
    iccssre
    mp2an
    @2
    cq
    @29
    cin
    #
    @29
    @8
    cq
    @29
    inss2
    wph
    cn
    @32
    @0
    cG
    wph
    cn
    @32
    cG
    wf1o
    cn
    @32
    cG
    wf
    #
    vitali.5
    cn
    @32
    cG
    f1of
    syl
    #
    ffvelrnda
    sseldi
    sseldi
    @2
    @11
    eqidd
    ovolshft
    eqtr4d
    #
    wph
    cc0
    @6
    wceq
    #
    @1
    wph
    cc0
    @6
    clt
    wbr
    #
    wn
    @36
    wph
    @37
    c3
    @21
    covol
    cfv
    #
    clt
    wbr
    #
    wph
    @37
    wa
    #
    c3
    c3
    @6
    cdiv
    co
    #
    cfl
    cfv
    #
    c1
    caddc
    co
    #
    @6
    cmul
    co
    #
    @38
    c3
    cxr
    wcel
    #
    @40
    c3
    3re
    rexri
    #
    a1i
    @40
    @44
    @40
    @43
    @6
    @40
    @43
    @40
    @42
    cn0
    wcel
    #
    @43
    cn
    wcel
    #
    @40
    @41
    cr
    wcel
    #
    cc0
    @41
    cle
    wbr
    @47
    @40
    @41
    @40
    c3
    crp
    wcel
    #
    @6
    crp
    wcel
    @41
    crp
    wcel
    c3
    cn
    wcel
    @50
    3nn
    c3
    nnrp
    ax-mp
    @40
    @6
    wph
    @6
    cr
    wcel
    #
    @37
    wph
    @20
    @51
    @27
    @20
    @19
    cr
    wss
    @19
    covol
    cfv
    #
    cr
    wcel
    @51
    unitssre
    @52
    c1
    cr
    @52
    c1
    cc0
    cmin
    co
    #
    c1
    cc0
    cr
    wcel
    @31
    cc0
    c1
    cle
    wbr
    @52
    @53
    wceq
    0re
    1re
    0le1
    cc0
    c1
    ovolicc
    mp3an
    1m0e1
    eqtri
    1re
    eqeltri
    @5
    @19
    ovolsscl
    mp3an23
    syl
    #
    adantr
    #
    wph
    @37
    simpr
    elrpd
    #
    c3
    @6
    rpdivcl
    sylancr
    #
    rpred
    #
    @40
    @41
    @57
    rpge0d
    @41
    flge0nn0
    syl2anc
    @42
    nn0p1nn
    syl
    #
    nnred
    #
    @55
    remulcld
    rexrd
    wph
    @38
    cxr
    wcel
    #
    @37
    wph
    @21
    cvol
    cdm
    #
    wcel
    #
    @21
    cr
    wss
    @61
    wph
    @3
    @62
    wcel
    #
    vm
    cn
    wral
    @63
    wph
    @64
    vm
    cn
    wph
    cn
    @62
    @0
    cT
    wph
    vn
    cn
    @16
    @62
    cT
    wph
    @12
    cn
    wcel
    #
    wa
    @5
    @62
    wcel
    #
    @13
    cr
    wcel
    @16
    @62
    wcel
    wph
    @66
    @65
    wph
    @66
    @5
    cr
    cpw
    #
    @62
    cdif
    wcel
    #
    vitali.7
    wph
    @66
    wn
    #
    @68
    wph
    @69
    wa
    @5
    @67
    wcel
    #
    @69
    wa
    @68
    wph
    @70
    @69
    wph
    @18
    @70
    @28
    @5
    cr
    reex
    elpw2
    sylibr
    anim1i
    @5
    @67
    @62
    eldif
    sylibr
    ex
    mt3d
    adantr
    wph
    cn
    cr
    @12
    cG
    wph
    @33
    @32
    cr
    wss
    cn
    cr
    cG
    wf
    @34
    @32
    cq
    cr
    cq
    @29
    inss1
    qssre
    sstri
    cn
    @32
    cr
    cG
    fss
    sylancl
    ffvelrnda
    vs
    @5
    @13
    shftmbl
    syl2anc
    vitali.6
    fmptd
    ffvelrnda
    #
    ralrimiva
    @3
    vm
    iunmbl
    syl
    #
    @21
    mblss
    @21
    ovolcl
    3syl
    adantr
    #
    @40
    @41
    @43
    clt
    wbr
    #
    c3
    @44
    clt
    wbr
    @40
    @49
    @74
    @58
    @41
    flltp1
    syl
    @40
    c3
    @43
    @6
    c3
    cr
    wcel
    @40
    3re
    a1i
    @60
    @56
    ltdivmul2d
    mpbid
    @40
    @44
    caddc
    vm
    cn
    @3
    cvol
    cfv
    #
    cmpt
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
    @38
    cle
    @40
    @78
    cxr
    wss
    @44
    @78
    wcel
    @44
    @79
    cle
    wbr
    @40
    @78
    cr
    cxr
    @40
    cn
    cr
    @77
    wf
    #
    @78
    cr
    wss
    @40
    vk
    @76
    c1
    cn
    nnuz
    @40
    1zzd
    @40
    cn
    cr
    vk
    cv
    @76
    @40
    vm
    cn
    @75
    cr
    @76
    wph
    @1
    @75
    cr
    wcel
    #
    @37
    @2
    @75
    @6
    cr
    @2
    @75
    @4
    @6
    @2
    @64
    @75
    @4
    wceq
    @71
    @3
    mblvol
    syl
    @35
    eqtrd
    #
    wph
    @51
    @1
    @54
    adantr
    eqeltrd
    #
    adantlr
    @76
    eqid
    #
    fmptd
    ffvelrnda
    serfre
    #
    cn
    cr
    @77
    frn
    syl
    ressxr
    syl6ss
    @40
    @43
    @77
    cfv
    #
    @44
    @78
    @40
    @86
    @43
    caddc
    cn
    @6
    csn
    cxp
    #
    c1
    cseq
    #
    cfv
    #
    @44
    @40
    @43
    @77
    @88
    @40
    @76
    @87
    caddc
    c1
    @40
    @76
    vm
    cn
    @6
    cmpt
    @87
    @40
    vm
    cn
    @75
    @6
    wph
    @1
    @75
    @6
    wceq
    @37
    @82
    adantlr
    mpteq2dva
    vm
    cn
    @6
    fconstmpt
    syl6eqr
    seqeq3d
    fveq1d
    @40
    @6
    cc
    wcel
    @48
    @89
    @44
    wceq
    @40
    @6
    @55
    recnd
    @59
    @6
    @43
    ser1const
    syl2anc
    eqtrd
    @40
    @77
    cn
    wfn
    #
    @48
    @86
    @78
    wcel
    @40
    @80
    @90
    @85
    cn
    cr
    @77
    ffn
    syl
    @59
    cn
    @43
    @77
    fnfvelrn
    syl2anc
    eqeltrrd
    @78
    @44
    supxrub
    syl2anc
    @40
    @21
    cvol
    cfv
    #
    @38
    @79
    @40
    @63
    @91
    @38
    wceq
    wph
    @63
    @37
    @72
    adantr
    @21
    mblvol
    syl
    @40
    @64
    @81
    wa
    #
    vm
    cn
    wral
    #
    vm
    cn
    @3
    wdisj
    #
    @91
    @79
    wceq
    wph
    @93
    @37
    wph
    @92
    vm
    cn
    @2
    @64
    @81
    @71
    @83
    jca
    ralrimiva
    adantr
    wph
    @94
    @37
    wph
    vx
    vy
    vz
    c.sm
    cS
    cT
    vm
    vn
    cF
    cG
    vs
    vitali.1
    vitali.2
    vitali.3
    vitali.4
    vitali.5
    vitali.6
    vitali.7
    vitalilem3
    adantr
    @3
    @77
    vm
    @76
    @77
    eqid
    @84
    voliun
    syl2anc
    eqtr3d
    breqtrrd
    xrltletrd
    @40
    @38
    c3
    cle
    wbr
    #
    @39
    wn
    #
    @40
    @38
    @24
    covol
    cfv
    #
    c3
    cle
    @40
    @25
    @24
    cr
    wss
    #
    @38
    @97
    cle
    wbr
    wph
    @25
    @37
    wph
    @20
    @22
    @25
    @26
    simp3d
    adantr
    @30
    c2
    cr
    wcel
    #
    @98
    neg1rr
    2re
    @23
    c2
    iccssre
    mp2an
    @21
    @24
    ovolss
    sylancl
    c2
    @23
    cmin
    co
    #
    c2
    c1
    caddc
    co
    @97
    c3
    c2
    c1
    2cn
    ax-1cn
    subnegi
    @30
    @99
    @23
    c2
    cle
    wbr
    @97
    @100
    wceq
    neg1rr
    2re
    @23
    c2
    neg1rr
    2re
    @23
    cc0
    clt
    wbr
    cc0
    c2
    clt
    wbr
    @23
    c2
    clt
    wbr
    neg1lt0
    2pos
    @23
    cc0
    c2
    neg1rr
    0re
    2re
    lttri
    mp2an
    ltleii
    @23
    c2
    ovolicc
    mp3an
    df-3
    3eqtr4i
    syl6breq
    @40
    @61
    @45
    @95
    @96
    wb
    @73
    @46
    @38
    c3
    xrlenlt
    sylancl
    mpbid
    pm2.65da
    wph
    @37
    @36
    wph
    cc0
    @6
    cle
    wbr
    #
    @37
    @36
    wo
    #
    wph
    @18
    @101
    @28
    @5
    ovolge0
    syl
    wph
    cc0
    cxr
    wcel
    @6
    cxr
    wcel
    #
    @101
    @102
    wb
    0xr
    wph
    @18
    @103
    @28
    @5
    ovolcl
    syl
    cc0
    @6
    xrleloe
    sylancr
    mpbid
    ord
    mpd
    adantr
    eqtr4d
end
