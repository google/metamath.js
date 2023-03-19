include "cioo.mm"
include "co.mm"
include "cres.mm"
include "cv.mm"
include "caddc.mm"
include "cfv.mm"
include "cc0.mm"
include "clt.mm"
include "wbr.mm"
include "cif.mm"
include "cmin.mm"
include "c1.mm"
include "cdiv.mm"
include "cmul.mm"
include "cmpt.mm"
include "cc.mm"
include "ccncf.mm"
include "cpi.mm"
include "cneg.mm"
include "cicc.mm"
include "wceq.mm"
include "reseq1i.mm"
include "a1i.mm"
include "wcel.mm"
include "wa.mm"
include "cr.mm"
include "pire.mm"
include "renegcli.mm"
include "elioore.mm"
include "adantl.mm"
include "iccssred.mm"
include "sseldd.mm"
include "adantr.mm"
include "cle.mm"
include "elicc2i.mm"
include "simp2bi.mm"
include "syl.mm"
include "cxr.mm"
include "rexrd.mm"
include "simpr.mm"
include "ioogtlb.mm"
include "syl3anc.mm"
include "lelttrd.mm"
include "ltled.mm"
include "iooltub.mm"
include "simp3bi.mm"
include "ltletrd.mm"
include "eliccd.mm"
include "ex.mm"
include "ssrdv.mm"
include "resmptd.mm"
include "eleq1.mm"
include "biimpac.mm"
include "adantll.mm"
include "wn.mm"
include "ad2antrr.mm"
include "pm2.65da.mm"
include "iffalsed.mm"
include "wf.mm"
include "readdcld.mm"
include "ffvelrnd.mm"
include "ifcld.mm"
include "resubcld.mm"
include "recnd.mm"
include "neqned.mm"
include "divrecd.mm"
include "eqtrd.mm"
include "mpteq2dva.mm"
include "3eqtrd.mm"
include "negsubd.mm"
include "eqcomd.mm"
include "addcomd.mm"
include "ltadd2dd.mm"
include "eqbrtrd.mm"
include "breqtrd.mm"
include "eliood.mm"
include "fvres.mm"
include "wss.mm"
include "ioosscn.mm"
include "fourierdlem23.mm"
include "eqeltrd.mm"
include "0red.mm"
include "simplr.mm"
include "adantlr.mm"
include "iftrued.mm"
include "negeqd.mm"
include "renegcld.mm"
include "ssid.mm"
include "constcncfg.mm"
include "ltnled.mm"
include "mpbird.mm"
include "condan.mm"
include "ltnsymd.mm"
include "negcld.mm"
include "syldan.mm"
include "pm2.61dan.mm"
include "addcncf.mm"
include "csn.mm"
include "cdif.mm"
include "eqid.mm"
include "1cnd.mm"
include "cdivcncf.mm"
include "wral.mm"
include "velsn.mm"
include "sylnibr.mm"
include "eldifd.mm"
include "ralrimiva.mm"
include "dfss3.mm"
include "sylibr.mm"
include "rereccld.mm"
include "cncfmptssg.mm"
include "mulcncf.mm"

theorem fourierdlem40
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cF: class F
  let cH: class H
  let cW: class W
  let cX: class X
  let cY: class Y
  let vs: setvar s
  let vk: setvar k
  let vx: setvar x
  assume fourierdlem40.f: |- ( ph -> F : RR --> RR )
  assume fourierdlem40.a: |- ( ph -> A e. ( -u _pi [,] _pi ) )
  assume fourierdlem40.b: |- ( ph -> B e. ( -u _pi [,] _pi ) )
  assume fourierdlem40.x: |- ( ph -> X e. RR )
  assume fourierdlem40.nxelab: |- ( ph -> -. 0 e. ( A (,) B ) )
  assume fourierdlem40.fcn: |- ( ph -> ( F |` ( ( A + X ) (,) ( B + X ) ) ) e. ( ( ( A + X ) (,) ( B + X ) ) -cn-> CC ) )
  assume fourierdlem40.y: |- ( ph -> Y e. RR )
  assume fourierdlem40.w: |- ( ph -> W e. RR )
  assume fourierdlem40.h: |- H = ( s e. ( -u _pi [,] _pi ) |-> if ( s = 0 , 0 , ( ( ( F ` ( X + s ) ) - if ( 0 < s , Y , W ) ) / s ) ) )

  disjoint A s
  disjoint B s
  disjoint F s
  disjoint W s
  disjoint X s
  disjoint Y s
  disjoint ph s
  disjoint k x
  assert |- ( ph -> ( H |` ( A (,) B ) ) e. ( ( A (,) B ) -cn-> CC ) )

  proof
    wph
    cH
    cA
    cB
    cioo
    co
    #
    cres
    #
    vs
    @0
    cX
    vs
    cv
    #
    caddc
    co
    #
    cF
    cfv
    #
    cc0
    @2
    clt
    wbr
    #
    cY
    cW
    cif
    #
    cmin
    co
    #
    c1
    @2
    cdiv
    co
    #
    cmul
    co
    #
    cmpt
    #
    @0
    cc
    ccncf
    co
    #
    wph
    @1
    vs
    cpi
    cneg
    #
    cpi
    cicc
    co
    #
    @2
    cc0
    wceq
    #
    cc0
    @7
    @2
    cdiv
    co
    #
    cif
    #
    cmpt
    #
    @0
    cres
    #
    vs
    @0
    @16
    cmpt
    @10
    @1
    @18
    wceq
    wph
    cH
    @17
    @0
    fourierdlem40.h
    reseq1i
    a1i
    wph
    vs
    @13
    @0
    @16
    wph
    vs
    @0
    @13
    wph
    @2
    @0
    wcel
    #
    @2
    @13
    wcel
    wph
    @19
    wa
    #
    @12
    cpi
    @2
    @12
    cr
    wcel
    #
    @20
    cpi
    pire
    renegcli
    #
    a1i
    #
    cpi
    cr
    wcel
    #
    @20
    pire
    a1i
    #
    @19
    @2
    cr
    wcel
    #
    wph
    @2
    cA
    cB
    elioore
    #
    adantl
    #
    @20
    @12
    @2
    @23
    @28
    @20
    @12
    cA
    @2
    @23
    wph
    cA
    cr
    wcel
    #
    @19
    wph
    @13
    cr
    cA
    wph
    @12
    cpi
    @21
    wph
    @22
    a1i
    @24
    wph
    pire
    a1i
    iccssred
    #
    fourierdlem40.a
    sseldd
    #
    adantr
    #
    @28
    wph
    @12
    cA
    cle
    wbr
    #
    @19
    wph
    cA
    @13
    wcel
    #
    @33
    fourierdlem40.a
    @34
    @29
    @33
    cA
    cpi
    cle
    wbr
    @12
    cpi
    cA
    @22
    pire
    elicc2i
    simp2bi
    syl
    adantr
    @20
    cA
    cxr
    wcel
    #
    cB
    cxr
    wcel
    #
    @19
    cA
    @2
    clt
    wbr
    #
    @20
    cA
    @32
    rexrd
    #
    wph
    @36
    @19
    wph
    cB
    wph
    @13
    cr
    cB
    @30
    fourierdlem40.b
    sseldd
    #
    rexrd
    #
    adantr
    #
    wph
    @19
    simpr
    #
    cA
    cB
    @2
    ioogtlb
    syl3anc
    #
    lelttrd
    ltled
    @20
    @2
    cpi
    @28
    @25
    @20
    @2
    cB
    cpi
    @28
    wph
    cB
    cr
    wcel
    #
    @19
    @39
    adantr
    #
    @25
    @20
    @35
    @36
    @19
    @2
    cB
    clt
    wbr
    #
    @38
    @41
    @42
    cA
    cB
    @2
    iooltub
    syl3anc
    #
    wph
    cB
    cpi
    cle
    wbr
    #
    @19
    wph
    cB
    @13
    wcel
    #
    @48
    fourierdlem40.b
    @49
    @44
    @12
    cB
    cle
    wbr
    @48
    @12
    cpi
    cB
    @22
    pire
    elicc2i
    simp3bi
    syl
    adantr
    ltletrd
    ltled
    eliccd
    ex
    ssrdv
    resmptd
    wph
    vs
    @0
    @16
    @9
    @20
    @16
    @15
    @9
    @20
    @14
    cc0
    @15
    @20
    @14
    cc0
    @0
    wcel
    #
    @19
    @14
    @50
    wph
    @14
    @19
    @50
    @2
    cc0
    @0
    eleq1
    biimpac
    adantll
    wph
    @50
    wn
    #
    @19
    @14
    fourierdlem40.nxelab
    ad2antrr
    pm2.65da
    #
    iffalsed
    @20
    @7
    @2
    @20
    @7
    @20
    @4
    @6
    @20
    cr
    cr
    @3
    cF
    wph
    cr
    cr
    cF
    wf
    @19
    fourierdlem40.f
    adantr
    @20
    cX
    @2
    wph
    cX
    cr
    wcel
    @19
    fourierdlem40.x
    adantr
    #
    @28
    readdcld
    #
    ffvelrnd
    #
    wph
    @6
    cr
    wcel
    @19
    wph
    @5
    cY
    cW
    cr
    fourierdlem40.y
    fourierdlem40.w
    ifcld
    adantr
    #
    resubcld
    recnd
    @20
    @2
    @28
    recnd
    #
    @20
    @2
    cc0
    @52
    neqned
    #
    divrecd
    eqtrd
    mpteq2dva
    3eqtrd
    wph
    vs
    @7
    @8
    @0
    wph
    vs
    @0
    @7
    cmpt
    vs
    @0
    @4
    @6
    cneg
    #
    caddc
    co
    #
    cmpt
    @11
    wph
    vs
    @0
    @7
    @60
    @20
    @60
    @7
    @20
    @4
    @6
    @20
    @4
    @55
    recnd
    @20
    @6
    @56
    recnd
    negsubd
    eqcomd
    mpteq2dva
    wph
    vs
    @4
    @59
    @0
    wph
    vs
    @0
    @4
    cmpt
    vs
    @0
    @3
    cF
    cA
    cX
    caddc
    co
    #
    cB
    cX
    caddc
    co
    #
    cioo
    co
    #
    cres
    #
    cfv
    #
    cmpt
    @11
    wph
    vs
    @0
    @4
    @65
    @20
    @65
    @4
    @20
    @3
    @63
    wcel
    @65
    @4
    wceq
    @20
    @61
    @62
    @3
    wph
    @61
    cxr
    wcel
    @19
    wph
    @61
    wph
    cA
    cX
    @31
    fourierdlem40.x
    readdcld
    rexrd
    adantr
    wph
    @62
    cxr
    wcel
    @19
    wph
    @62
    wph
    cB
    cX
    @39
    fourierdlem40.x
    readdcld
    rexrd
    adantr
    @54
    @20
    @61
    cX
    cA
    caddc
    co
    #
    @3
    clt
    wph
    @61
    @66
    wceq
    @19
    wph
    cA
    cX
    wph
    cA
    @31
    recnd
    wph
    cX
    fourierdlem40.x
    recnd
    #
    addcomd
    adantr
    @20
    cA
    @2
    cX
    @32
    @28
    @53
    @43
    ltadd2dd
    eqbrtrd
    @20
    @3
    cX
    cB
    caddc
    co
    #
    @62
    clt
    @20
    @2
    cB
    cX
    @28
    @45
    @53
    @47
    ltadd2dd
    wph
    @68
    @62
    wceq
    @19
    wph
    cX
    cB
    @67
    wph
    cB
    @39
    recnd
    addcomd
    adantr
    breqtrd
    eliood
    #
    @3
    @63
    cF
    fvres
    syl
    eqcomd
    mpteq2dva
    wph
    @63
    @0
    @64
    cX
    vs
    @63
    cc
    wss
    wph
    @61
    @62
    ioosscn
    a1i
    fourierdlem40.fcn
    @0
    cc
    wss
    wph
    cA
    cB
    ioosscn
    a1i
    #
    @67
    @69
    fourierdlem23
    eqeltrd
    wph
    cc0
    cA
    cle
    wbr
    #
    vs
    @0
    @59
    cmpt
    #
    @11
    wcel
    #
    wph
    @71
    wa
    #
    @72
    vs
    @0
    cY
    cneg
    #
    cmpt
    #
    @11
    @74
    vs
    @0
    @59
    @75
    @74
    @19
    wa
    #
    @6
    cY
    @77
    @5
    cY
    cW
    @77
    cc0
    cA
    @2
    @77
    0red
    wph
    @29
    @71
    @19
    @31
    ad2antrr
    @19
    @26
    @74
    @27
    adantl
    wph
    @71
    @19
    simplr
    wph
    @19
    @37
    @71
    @43
    adantlr
    lelttrd
    iftrued
    negeqd
    mpteq2dva
    wph
    @76
    @11
    wcel
    @71
    wph
    vs
    @0
    @75
    cc
    @70
    wph
    @75
    wph
    cY
    fourierdlem40.y
    renegcld
    recnd
    cc
    cc
    wss
    wph
    cc
    ssid
    a1i
    #
    constcncfg
    adantr
    eqeltrd
    wph
    @71
    wn
    #
    cB
    cc0
    cle
    wbr
    #
    @73
    wph
    @79
    wa
    #
    @80
    @50
    @81
    @80
    wn
    #
    wa
    #
    cA
    cB
    cc0
    wph
    @35
    @79
    @82
    wph
    cA
    @31
    rexrd
    ad2antrr
    wph
    @36
    @79
    @82
    @40
    ad2antrr
    @83
    0red
    @81
    cA
    cc0
    clt
    wbr
    #
    @82
    @81
    @84
    @79
    wph
    @79
    simpr
    @81
    cA
    cc0
    wph
    @29
    @79
    @31
    adantr
    @81
    0red
    ltnled
    mpbird
    adantr
    wph
    @82
    cc0
    cB
    clt
    wbr
    #
    @79
    wph
    @82
    wa
    #
    @85
    @82
    wph
    @82
    simpr
    @86
    cc0
    cB
    @86
    0red
    wph
    @44
    @82
    @39
    adantr
    ltnled
    mpbird
    adantlr
    eliood
    wph
    @51
    @79
    @82
    fourierdlem40.nxelab
    ad2antrr
    condan
    wph
    @80
    wa
    #
    @72
    vs
    @0
    cW
    cneg
    #
    cmpt
    #
    @11
    @87
    vs
    @0
    @59
    @88
    @87
    @19
    wa
    #
    @6
    cW
    @90
    @5
    cY
    cW
    @90
    @2
    cc0
    @19
    @26
    @87
    @27
    adantl
    #
    @90
    0red
    #
    @90
    @2
    cB
    cc0
    @91
    wph
    @44
    @80
    @19
    @39
    ad2antrr
    @92
    wph
    @19
    @46
    @80
    @47
    adantlr
    wph
    @80
    @19
    simplr
    ltletrd
    ltnsymd
    iffalsed
    negeqd
    mpteq2dva
    wph
    @89
    @11
    wcel
    @80
    wph
    vs
    @0
    @88
    cc
    @70
    wph
    cW
    wph
    cW
    fourierdlem40.w
    recnd
    negcld
    @78
    constcncfg
    adantr
    eqeltrd
    syldan
    pm2.61dan
    addcncf
    eqeltrd
    wph
    vs
    cc
    cc0
    csn
    #
    cdif
    #
    cc
    @0
    cc
    @8
    vs
    @94
    @8
    cmpt
    #
    @95
    eqid
    #
    wph
    c1
    cc
    wcel
    @95
    @94
    cc
    ccncf
    co
    wcel
    wph
    1cnd
    vs
    c1
    @95
    @96
    cdivcncf
    syl
    wph
    @2
    @94
    wcel
    #
    vs
    @0
    wral
    @0
    @94
    wss
    wph
    @97
    vs
    @0
    @20
    @2
    cc
    @93
    @57
    @20
    @14
    @2
    @93
    wcel
    @52
    vs
    cc0
    velsn
    sylnibr
    eldifd
    ralrimiva
    vs
    @0
    @94
    dfss3
    sylibr
    @78
    @20
    @8
    @20
    @2
    @28
    @58
    rereccld
    recnd
    cncfmptssg
    mulcncf
    eqeltrd
end
