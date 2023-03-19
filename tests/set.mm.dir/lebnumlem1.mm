include "cv.mm"
include "cdif.mm"
include "co.mm"
include "cmpt.mm"
include "crn.mm"
include "cxr.mm"
include "clt.mm"
include "cinf.mm"
include "csu.mm"
include "crp.mm"
include "wcel.mm"
include "wa.mm"
include "cfn.mm"
include "adantr.mm"
include "cr.mm"
include "wral.mm"
include "wf.mm"
include "cme.mm"
include "cfv.mm"
include "wss.mm"
include "c0.mm"
include "wne.mm"
include "ad2antrr.mm"
include "difssd.mm"
include "cuni.mm"
include "sselda.mm"
include "elssuni.mm"
include "syl.mm"
include "wceq.mm"
include "cxmt.mm"
include "metxmet.mm"
include "mopnuni.mm"
include "sseqtr4d.mm"
include "wi.mm"
include "wn.mm"
include "eleq1.mm"
include "notbid.mm"
include "syl5ibrcom.mm"
include "necon2ad.mm"
include "imp.mm"
include "pssdifn0.mm"
include "syl2anc.mm"
include "eqid.mm"
include "metdsre.mm"
include "syl3anc.mm"
include "fmpt.mm"
include "sylibr.mm"
include "simplr.mm"
include "rsp.mm"
include "sylc.mm"
include "fsumrecl.mm"
include "cc0.mm"
include "wbr.mm"
include "wrex.mm"
include "eleq2d.mm"
include "biimpa.mm"
include "eluni2.mm"
include "sylib.mm"
include "0red.mm"
include "metdsval.mm"
include "simprl.mm"
include "sseldd.mm"
include "3syl.mm"
include "mpd.mm"
include "ffvelrnd.mm"
include "eqeltrrd.mm"
include "cle.mm"
include "cpnf.mm"
include "cicc.mm"
include "metdsf.mm"
include "elxrge0.mm"
include "simprd.mm"
include "ccl.mm"
include "elndif.mm"
include "ad2antll.mm"
include "ccld.mm"
include "difeq1d.mm"
include "ctop.mm"
include "mopntop.mm"
include "opncld.mm"
include "eqeltrd.mm"
include "cldcls.mm"
include "neleqtrrd.mm"
include "wb.mm"
include "metdseq0.mm"
include "necon3abid.mm"
include "mpbird.mm"
include "ne0gt0d.mm"
include "breqtrd.mm"
include "adantlr.mm"
include "difeq2.mm"
include "mpteq1d.mm"
include "rneqd.mm"
include "infeq1d.mm"
include "fsumge1.mm"
include "ltletrd.mm"
include "rexlimddv.mm"
include "elrpd.mm"
include "fmptd.mm"

theorem lebnumlem1
  let wph: wff ph
  let vy: setvar y
  let vz: setvar z
  let cD: class D
  let cU: class U
  let vk: setvar k
  let cF: class F
  let cJ: class J
  let cX: class X
  let vd: setvar d
  let vm: setvar m
  let vr: setvar r
  let vu: setvar u
  let vw: setvar w
  let vx: setvar x
  let cK: class K
  assume lebnum.j: |- J = ( MetOpen ` D )
  assume lebnum.d: |- ( ph -> D e. ( Met ` X ) )
  assume lebnum.c: |- ( ph -> J e. Comp )
  assume lebnum.s: |- ( ph -> U C_ J )
  assume lebnum.u: |- ( ph -> X = U. U )
  assume lebnumlem1.u: |- ( ph -> U e. Fin )
  assume lebnumlem1.n: |- ( ph -> -. X e. U )
  assume lebnumlem1.f: |- F = ( y e. X |-> sum_ k e. U inf ( ran ( z e. ( X \ k ) |-> ( y D z ) ) , RR* , < ) )

  disjoint k y
  disjoint k z
  disjoint D k
  disjoint y z
  disjoint D y
  disjoint D z
  disjoint J k
  disjoint J y
  disjoint J z
  disjoint U k
  disjoint U y
  disjoint U z
  disjoint k ph
  disjoint ph y
  disjoint ph z
  disjoint X k
  disjoint X y
  disjoint X z
  disjoint d k
  disjoint d m
  disjoint d r
  disjoint d u
  disjoint d w
  disjoint d x
  disjoint d y
  disjoint d z
  disjoint D d
  disjoint k m
  disjoint k r
  disjoint k u
  disjoint k w
  disjoint k x
  disjoint m r
  disjoint m u
  disjoint m w
  disjoint m x
  disjoint m y
  disjoint m z
  disjoint D m
  disjoint r u
  disjoint r w
  disjoint r x
  disjoint r y
  disjoint r z
  disjoint D r
  disjoint u w
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint D u
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint D w
  disjoint x y
  disjoint x z
  disjoint D x
  disjoint J d
  disjoint J w
  disjoint J x
  disjoint U d
  disjoint U m
  disjoint U r
  disjoint U u
  disjoint U w
  disjoint U x
  disjoint F r
  disjoint F w
  disjoint F x
  disjoint d ph
  disjoint m ph
  disjoint ph r
  disjoint ph w
  disjoint ph x
  disjoint X d
  disjoint X m
  disjoint X r
  disjoint X u
  disjoint X w
  disjoint X x
  disjoint K x
  assert |- ( ph -> F : X --> RR+ )

  proof
    wph
    vy
    cX
    cU
    vz
    cX
    vk
    cv
    #
    cdif
    #
    vy
    cv
    #
    vz
    cv
    #
    cD
    co
    #
    cmpt
    #
    crn
    #
    cxr
    clt
    cinf
    #
    vk
    csu
    #
    crp
    cF
    wph
    @2
    cX
    wcel
    #
    wa
    #
    @8
    @10
    cU
    @7
    vk
    wph
    cU
    cfn
    wcel
    #
    @9
    lebnumlem1.u
    adantr
    @10
    @0
    cU
    wcel
    #
    wa
    #
    @7
    cr
    wcel
    #
    vy
    cX
    wral
    #
    @9
    @14
    @13
    cX
    cr
    vy
    cX
    @7
    cmpt
    #
    wf
    #
    @15
    @13
    cD
    cX
    cme
    cfv
    wcel
    #
    @1
    cX
    wss
    #
    @1
    c0
    wne
    #
    @17
    wph
    @18
    @9
    @12
    lebnum.d
    ad2antrr
    @13
    cX
    @0
    difssd
    #
    @13
    @0
    cX
    wss
    @0
    cX
    wne
    #
    @20
    @13
    @0
    cJ
    cuni
    #
    cX
    @13
    @0
    cJ
    wcel
    @0
    @23
    wss
    @10
    cU
    cJ
    @0
    wph
    cU
    cJ
    wss
    #
    @9
    lebnum.s
    adantr
    sselda
    @0
    cJ
    elssuni
    syl
    wph
    cX
    @23
    wceq
    #
    @9
    @12
    wph
    cD
    cX
    cxmt
    cfv
    wcel
    #
    @25
    wph
    @18
    @26
    lebnum.d
    cD
    cX
    metxmet
    #
    syl
    #
    cD
    cJ
    cX
    lebnum.j
    mopnuni
    #
    syl
    ad2antrr
    sseqtr4d
    @10
    @12
    @22
    wph
    @12
    @22
    wi
    @9
    wph
    @12
    @0
    cX
    wph
    @12
    wn
    @0
    cX
    wceq
    #
    cX
    cU
    wcel
    #
    wn
    #
    lebnumlem1.n
    @30
    @12
    @31
    @0
    cX
    cU
    eleq1
    notbid
    syl5ibrcom
    necon2ad
    adantr
    imp
    @0
    cX
    pssdifn0
    syl2anc
    vy
    vz
    cD
    @1
    @16
    cX
    @16
    eqid
    #
    metdsre
    syl3anc
    vy
    cX
    cr
    @7
    @16
    @33
    fmpt
    sylibr
    wph
    @9
    @12
    simplr
    #
    @14
    vy
    cX
    rsp
    sylc
    #
    fsumrecl
    #
    @10
    @2
    vm
    cv
    #
    wcel
    #
    cc0
    @8
    clt
    wbr
    vm
    cU
    @10
    @2
    cU
    cuni
    #
    wcel
    #
    @38
    vm
    cU
    wrex
    wph
    @9
    @40
    wph
    cX
    @39
    @2
    lebnum.u
    eleq2d
    biimpa
    vm
    @2
    cU
    eluni2
    sylib
    @10
    @37
    cU
    wcel
    #
    @38
    wa
    #
    wa
    #
    cc0
    vz
    cX
    @37
    cdif
    #
    @4
    cmpt
    #
    crn
    #
    cxr
    clt
    cinf
    #
    @8
    @43
    0red
    @43
    @2
    vw
    cX
    vz
    @44
    vw
    cv
    @3
    cD
    co
    cmpt
    crn
    cxr
    clt
    cinf
    cmpt
    #
    cfv
    #
    @47
    cr
    @43
    @9
    @49
    @47
    wceq
    wph
    @9
    @42
    simplr
    #
    vw
    vz
    @2
    cD
    @44
    @48
    cX
    @48
    eqid
    #
    metdsval
    syl
    #
    @43
    cX
    cr
    @2
    @48
    @43
    @18
    @44
    cX
    wss
    #
    @44
    c0
    wne
    #
    cX
    cr
    @48
    wf
    wph
    @18
    @9
    @42
    lebnum.d
    ad2antrr
    #
    @43
    cX
    @37
    difssd
    #
    @43
    @37
    cX
    wss
    @37
    cX
    wne
    #
    @54
    @43
    @37
    @23
    cX
    @43
    @37
    cJ
    wcel
    #
    @37
    @23
    wss
    @43
    cU
    cJ
    @37
    wph
    @24
    @9
    @42
    lebnum.s
    ad2antrr
    @10
    @41
    @38
    simprl
    #
    sseldd
    #
    @37
    cJ
    elssuni
    syl
    @43
    @18
    @26
    @25
    @55
    @27
    @29
    3syl
    #
    sseqtr4d
    @43
    @41
    @57
    @59
    wph
    @41
    @57
    wi
    @9
    @42
    wph
    @41
    @37
    cX
    wph
    @41
    wn
    @37
    cX
    wceq
    #
    @32
    lebnumlem1.n
    @62
    @41
    @31
    @37
    cX
    cU
    eleq1
    notbid
    syl5ibrcom
    necon2ad
    ad2antrr
    mpd
    @37
    cX
    pssdifn0
    syl2anc
    vw
    vz
    cD
    @44
    @48
    cX
    @51
    metdsre
    syl3anc
    @50
    ffvelrnd
    #
    eqeltrrd
    @10
    @8
    cr
    wcel
    @42
    @36
    adantr
    @43
    cc0
    @49
    @47
    clt
    @43
    @49
    @63
    @43
    @49
    cxr
    wcel
    #
    cc0
    @49
    cle
    wbr
    #
    @43
    @49
    cc0
    cpnf
    cicc
    co
    #
    wcel
    @64
    @65
    wa
    @43
    cX
    @66
    @2
    @48
    @43
    @26
    @53
    cX
    @66
    @48
    wf
    wph
    @26
    @9
    @42
    @28
    ad2antrr
    #
    @56
    vw
    vz
    cD
    @44
    @48
    cX
    @51
    metdsf
    syl2anc
    @50
    ffvelrnd
    @49
    elxrge0
    sylib
    simprd
    @43
    @49
    cc0
    wne
    @2
    @44
    cJ
    ccl
    cfv
    cfv
    #
    wcel
    #
    wn
    @43
    @68
    @44
    @2
    @38
    @2
    @44
    wcel
    wn
    @10
    @41
    @2
    @37
    cX
    elndif
    ad2antll
    @43
    @44
    cJ
    ccld
    cfv
    #
    wcel
    @68
    @44
    wceq
    @43
    @44
    @23
    @37
    cdif
    #
    @70
    @43
    cX
    @23
    @37
    @61
    difeq1d
    @43
    cJ
    ctop
    wcel
    #
    @58
    @71
    @70
    wcel
    @43
    @26
    @72
    @67
    cD
    cJ
    cX
    lebnum.j
    mopntop
    syl
    @60
    @37
    cJ
    @23
    @23
    eqid
    opncld
    syl2anc
    eqeltrd
    @44
    cJ
    cldcls
    syl
    neleqtrrd
    @43
    @69
    @49
    cc0
    @43
    @26
    @53
    @9
    @49
    cc0
    wceq
    @69
    wb
    @67
    @56
    @50
    vw
    vz
    @2
    cD
    @44
    @48
    cJ
    cX
    @51
    lebnum.j
    metdseq0
    syl3anc
    necon3abid
    mpbird
    ne0gt0d
    @52
    breqtrd
    @43
    cU
    @7
    @47
    vk
    @37
    wph
    @11
    @9
    @42
    lebnumlem1.u
    ad2antrr
    @10
    @12
    @14
    @42
    @35
    adantlr
    @10
    @12
    cc0
    @7
    cle
    wbr
    #
    @42
    @13
    @7
    cxr
    wcel
    #
    @73
    @13
    @7
    @66
    wcel
    #
    @74
    @73
    wa
    @13
    @75
    vy
    cX
    wral
    #
    @9
    @75
    @13
    cX
    @66
    @16
    wf
    #
    @76
    @13
    @26
    @19
    @77
    wph
    @26
    @9
    @12
    @28
    ad2antrr
    @21
    vy
    vz
    cD
    @1
    @16
    cX
    @33
    metdsf
    syl2anc
    vy
    cX
    @66
    @7
    @16
    @33
    fmpt
    sylibr
    @34
    @75
    vy
    cX
    rsp
    sylc
    @7
    elxrge0
    sylib
    simprd
    adantlr
    @0
    @37
    wceq
    #
    cxr
    @6
    @46
    clt
    @78
    @5
    @45
    @78
    vz
    @1
    @44
    @4
    @0
    @37
    cX
    difeq2
    mpteq1d
    rneqd
    infeq1d
    @59
    fsumge1
    ltletrd
    rexlimddv
    elrpd
    lebnumlem1.f
    fmptd
end
