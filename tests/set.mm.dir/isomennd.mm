include "come.mm"
include "wcel.mm"
include "cdm.mm"
include "cc0.mm"
include "cpnf.mm"
include "cicc.mm"
include "co.mm"
include "wf.mm"
include "cuni.mm"
include "cpw.mm"
include "wceq.mm"
include "wa.mm"
include "c0.mm"
include "cfv.mm"
include "cv.mm"
include "cle.mm"
include "wbr.mm"
include "wral.mm"
include "com.mm"
include "cdom.mm"
include "cres.mm"
include "csumge0.mm"
include "wi.mm"
include "id.mm"
include "fdm.mm"
include "feq2d.mm"
include "mpbird.mm"
include "syl.mm"
include "unipw.mm"
include "pweqi.mm"
include "a1i.mm"
include "unieqd.mm"
include "pweqd.mm"
include "3eqtr4rd.mm"
include "jca31.mm"
include "wss.mm"
include "simpl.mm"
include "simpr.mm"
include "eqtrd.mm"
include "adantr.mm"
include "eleqtrd.mm"
include "elpwi.mm"
include "adantrr.mm"
include "adantl.mm"
include "syl3anc.mm"
include "ralrimivva.mm"
include "0le0.mm"
include "unieq.mm"
include "uni0.mm"
include "fveq2d.mm"
include "reseq2.mm"
include "res0.mm"
include "sge00.mm"
include "breq12d.mm"
include "ad4ant14.mm"
include "wn.mm"
include "wne.mm"
include "neqne.mm"
include "cn.mm"
include "wf1o.mm"
include "wex.mm"
include "ssnnf1octb.mm"
include "adantll.mm"
include "cif.mm"
include "cmpt.mm"
include "ad2antrr.mm"
include "ciun.mm"
include "sylan.mm"
include "adantlr.mm"
include "simprl.mm"
include "simprr.mm"
include "eleq1.mm"
include "fveq2.mm"
include "ifbieq1d.mm"
include "cbvmptv.mm"
include "isomenndlem.mm"
include "ex.mm"
include "exlimdv.mm"
include "mpd.mm"
include "syl2anc.mm"
include "pm2.61dan.mm"
include "ralrimiva.mm"
include "cvv.mm"
include "wb.mm"
include "pwexg.mm"
include "fex.mm"
include "isome.mm"

theorem isomennd
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vn: setvar n
  let cO: class O
  let cV: class V
  let cX: class X
  let va: setvar a
  let vf: setvar f
  let vm: setvar m
  let vk: setvar k
  assume isomennd.x: |- ( ph -> X e. V )
  assume isomennd.o: |- ( ph -> O : ~P X --> ( 0 [,] +oo ) )
  assume isomennd.o0: |- ( ph -> ( O ` (/) ) = 0 )
  assume isomennd.le: |- ( ( ph /\ x C_ X /\ y C_ x ) -> ( O ` y ) <_ ( O ` x ) )
  assume isomennd.sa: |- ( ( ph /\ a : NN --> ~P X ) -> ( O ` U_ n e. NN ( a ` n ) ) <_ ( sum^ ` ( n e. NN |-> ( O ` ( a ` n ) ) ) ) )

  disjoint O a
  disjoint O n
  disjoint O x
  disjoint a n
  disjoint a x
  disjoint n x
  disjoint O y
  disjoint x y
  disjoint X a
  disjoint a ph
  disjoint n ph
  disjoint ph x
  disjoint ph y
  disjoint O f
  disjoint a f
  disjoint f n
  disjoint f x
  disjoint a m
  disjoint f m
  disjoint m n
  disjoint f ph
  disjoint k x
  assert |- ( ph -> O e. OutMeas )

  proof
    wph
    cO
    come
    wcel
    #
    cO
    cdm
    #
    cc0
    cpnf
    cicc
    co
    #
    cO
    wf
    #
    @1
    @1
    cuni
    #
    cpw
    #
    wceq
    #
    wa
    c0
    cO
    cfv
    #
    cc0
    wceq
    #
    wa
    #
    vy
    cv
    #
    cO
    cfv
    vx
    cv
    #
    cO
    cfv
    cle
    wbr
    #
    vy
    @11
    cpw
    #
    wral
    vx
    @5
    wral
    #
    wa
    @11
    com
    cdom
    wbr
    #
    @11
    cuni
    #
    cO
    cfv
    #
    cO
    @11
    cres
    #
    csumge0
    cfv
    #
    cle
    wbr
    #
    wi
    #
    vx
    @1
    cpw
    #
    wral
    #
    wa
    #
    wph
    @9
    @14
    @23
    wph
    @3
    @6
    @8
    wph
    cX
    cpw
    #
    @2
    cO
    wf
    #
    @3
    isomennd.o
    @26
    @3
    @26
    @26
    id
    @26
    @1
    @25
    @2
    cO
    @25
    @2
    cO
    fdm
    #
    feq2d
    mpbird
    syl
    wph
    @25
    cuni
    #
    cpw
    #
    @25
    @5
    @1
    @29
    @25
    wceq
    wph
    @28
    cX
    cX
    unipw
    pweqi
    a1i
    #
    wph
    @4
    @28
    wph
    @1
    @25
    wph
    @26
    @1
    @25
    wceq
    isomennd.o
    @27
    syl
    #
    unieqd
    pweqd
    #
    @31
    3eqtr4rd
    isomennd.o0
    jca31
    wph
    @12
    vx
    vy
    @5
    @13
    wph
    @11
    @5
    wcel
    #
    @10
    @13
    wcel
    #
    wa
    #
    wa
    wph
    @11
    cX
    wss
    #
    @10
    @11
    wss
    #
    @12
    wph
    @35
    simpl
    wph
    @33
    @36
    @34
    wph
    @33
    wa
    #
    @11
    @25
    wcel
    @36
    @38
    @11
    @5
    @25
    wph
    @33
    simpr
    wph
    @5
    @25
    wceq
    @33
    wph
    @5
    @29
    @25
    @32
    @30
    eqtrd
    adantr
    eleqtrd
    @11
    cX
    elpwi
    syl
    adantrr
    @35
    @37
    wph
    @34
    @37
    @33
    @10
    @11
    elpwi
    adantl
    adantl
    isomennd.le
    syl3anc
    ralrimivva
    wph
    @21
    vx
    @22
    wph
    @11
    @22
    wcel
    #
    wa
    #
    @15
    @20
    @40
    @15
    wa
    #
    @11
    c0
    wceq
    #
    @20
    wph
    @42
    @20
    @39
    @15
    wph
    @42
    wa
    #
    @20
    cc0
    cc0
    cle
    wbr
    #
    @44
    @43
    0le0
    a1i
    @43
    @17
    cc0
    @19
    cc0
    cle
    @43
    @17
    @7
    cc0
    @42
    @17
    @7
    wceq
    wph
    @42
    @16
    c0
    cO
    @42
    @16
    c0
    cuni
    #
    c0
    @11
    c0
    unieq
    @45
    c0
    wceq
    @42
    uni0
    a1i
    eqtrd
    fveq2d
    adantl
    wph
    @8
    @42
    isomennd.o0
    adantr
    eqtrd
    @42
    @19
    cc0
    wceq
    wph
    @42
    @19
    c0
    csumge0
    cfv
    #
    cc0
    @42
    @18
    c0
    csumge0
    @42
    @18
    cO
    c0
    cres
    #
    c0
    @11
    c0
    cO
    reseq2
    @47
    c0
    wceq
    @42
    cO
    res0
    a1i
    eqtrd
    fveq2d
    @46
    cc0
    wceq
    @42
    sge00
    a1i
    eqtrd
    adantl
    breq12d
    mpbird
    ad4ant14
    @41
    @42
    wn
    #
    wa
    @41
    @11
    c0
    wne
    #
    @20
    @41
    @48
    simpl
    @48
    @49
    @41
    @11
    c0
    neqne
    adantl
    @41
    @49
    wa
    #
    vf
    cv
    #
    cdm
    #
    cn
    wss
    #
    @52
    @11
    @51
    wf1o
    #
    wa
    #
    vf
    wex
    #
    @20
    @15
    @49
    @56
    @40
    @11
    vf
    ssnnf1octb
    adantll
    @50
    @55
    @20
    vf
    @40
    @55
    @20
    wi
    @15
    @49
    @40
    @55
    @20
    @40
    @55
    wa
    vm
    cn
    vm
    cv
    #
    @52
    wcel
    #
    @57
    @51
    cfv
    #
    c0
    cif
    #
    cmpt
    @52
    vn
    @51
    cO
    cX
    @11
    va
    wph
    @26
    @39
    @55
    isomennd.o
    ad2antrr
    wph
    @8
    @39
    @55
    isomennd.o0
    ad2antrr
    @40
    @11
    @25
    wss
    #
    @55
    @40
    @11
    @25
    cpw
    #
    wcel
    @61
    @40
    @11
    @22
    @62
    wph
    @39
    simpr
    wph
    @22
    @62
    wceq
    @39
    wph
    @1
    @25
    @31
    pweqd
    adantr
    eleqtrd
    @11
    @25
    elpwi
    syl
    adantr
    @40
    cn
    @25
    va
    cv
    #
    wf
    #
    vn
    cn
    vn
    cv
    #
    @63
    cfv
    #
    ciun
    cO
    cfv
    vn
    cn
    @66
    cO
    cfv
    cmpt
    csumge0
    cfv
    cle
    wbr
    #
    @55
    @40
    wph
    @64
    @67
    wph
    @39
    simpl
    isomennd.sa
    sylan
    adantlr
    @40
    @53
    @54
    simprl
    @40
    @53
    @54
    simprr
    vm
    vn
    cn
    @60
    @65
    @52
    wcel
    #
    @65
    @51
    cfv
    #
    c0
    cif
    @57
    @65
    wceq
    @58
    @68
    @59
    @69
    c0
    @57
    @65
    @52
    eleq1
    @57
    @65
    @51
    fveq2
    ifbieq1d
    cbvmptv
    isomenndlem
    ex
    ad2antrr
    exlimdv
    mpd
    syl2anc
    pm2.61dan
    ex
    ralrimiva
    jca31
    wph
    cO
    cvv
    wcel
    #
    @0
    @24
    wb
    wph
    @26
    @25
    cvv
    wcel
    #
    @70
    isomennd.o
    wph
    cX
    cV
    wcel
    @71
    isomennd.x
    cX
    cV
    pwexg
    syl
    @25
    @2
    cvv
    cO
    fex
    syl2anc
    vx
    vy
    cO
    cvv
    isome
    syl
    mpbird
end
