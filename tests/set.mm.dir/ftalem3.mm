include "cv.mm"
include "cfv.mm"
include "cabs.mm"
include "cle.mm"
include "wbr.mm"
include "wral.mm"
include "cc.mm"
include "wrex.mm"
include "wss.mm"
include "crab.mm"
include "ssrab2.mm"
include "eqsstri.mm"
include "ccom.mm"
include "cres.mm"
include "crest.mm"
include "co.mm"
include "cioo.mm"
include "crn.mm"
include "ctg.mm"
include "ctopon.mm"
include "wcel.mm"
include "cnfldtopon.mm"
include "resttopon.mm"
include "mp2an.mm"
include "toponunii.mm"
include "eqid.mm"
include "ccld.mm"
include "cr.mm"
include "ccmp.mm"
include "cmin.mm"
include "cxmt.mm"
include "cc0.mm"
include "cxr.mm"
include "cnxmet.mm"
include "a1i.mm"
include "0cn.mm"
include "rpxrd.mm"
include "cnfldtopn.mm"
include "wceq.mm"
include "cnmetdval.mm"
include "mpan.mm"
include "cneg.mm"
include "df-neg.mm"
include "fveq2i.mm"
include "absneg.mm"
include "syl5eqr.mm"
include "eqtrd.mm"
include "breq1d.mm"
include "rabbiia.mm"
include "eqtr4i.mm"
include "blcld.mm"
include "syl3anc.mm"
include "rpred.mm"
include "fveq2.mm"
include "elrab2.mm"
include "simprbi.mm"
include "rgen.mm"
include "breq2.mm"
include "ralbidv.mm"
include "rspcev.mm"
include "sylancl.mm"
include "wa.mm"
include "wb.mm"
include "cnheibor.mm"
include "ax-mp.mm"
include "sylanbrc.mm"
include "ccn.mm"
include "ccncf.mm"
include "cply.mm"
include "plycn.mm"
include "syl.mm"
include "abscncf.mm"
include "cncfco.mm"
include "ssid.mm"
include "ax-resscn.mm"
include "ctop.mm"
include "cnfldtop.mm"
include "restid.mm"
include "eqcomi.mm"
include "tgioo2.mm"
include "cncfcn.mm"
include "syl6eleq.mm"
include "cnrest.mm"
include "c0.mm"
include "wne.mm"
include "rpge0d.mm"
include "abs0.mm"
include "syl6eq.mm"
include "ne0i.mm"
include "evth2.mm"
include "fvres.mm"
include "ad2antlr.mm"
include "wf.mm"
include "plyf.mm"
include "ad2antrr.mm"
include "simplr.mm"
include "sseldi.mm"
include "fvco3.mm"
include "syl2anc.mm"
include "adantl.mm"
include "simpr.mm"
include "breq12d.mm"
include "ralbidva.mm"
include "rexbidva.mm"
include "mpbid.mm"
include "ssrexv.mm"
include "mpsyl.mm"
include "cdif.mm"
include "wi.mm"
include "adantr.mm"
include "fveq2d.mm"
include "breq2d.mm"
include "rspcv.mm"
include "ffvelrn.mm"
include "abscld.mm"
include "eldifad.mm"
include "ffvelrnd.mm"
include "clt.mm"
include "wn.mm"
include "eldifbd.mm"
include "baib.mm"
include "mtbid.mm"
include "ltnled.mm"
include "mpbird.mm"
include "rsp.mm"
include "syl3c.mm"
include "ltled.mm"
include "letr.mm"
include "mpan2d.mm"
include "ralrimdva.mm"
include "syld.mm"
include "ancld.mm"
include "cun.mm"
include "ralunb.mm"
include "undif2.mm"
include "ssequn1.mm"
include "mpbi.mm"
include "eqtri.mm"
include "raleqi.mm"
include "bitr3i.mm"
include "syl6ib.mm"
include "reximdva.mm"
include "mpd.mm"

theorem ftalem3
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cD: class D
  let cR: class R
  let cS: class S
  let cF: class F
  let cJ: class J
  let cN: class N
  let vk: setvar k
  let vn: setvar n
  let vr: setvar r
  let vs: setvar s
  let cE: class E
  let cK: class K
  let vw: setvar w
  let cT: class T
  let cU: class U
  let cX: class X
  assume ftalem.1: |- A = ( coeff ` F )
  assume ftalem.2: |- N = ( deg ` F )
  assume ftalem.3: |- ( ph -> F e. ( Poly ` S ) )
  assume ftalem.4: |- ( ph -> N e. NN )
  assume ftalem3.5: |- D = { y e. CC | ( abs ` y ) <_ R }
  assume ftalem3.6: |- J = ( TopOpen ` CCfld )
  assume ftalem3.7: |- ( ph -> R e. RR+ )
  assume ftalem3.8: |- ( ph -> A. x e. CC ( R < ( abs ` x ) -> ( abs ` ( F ` 0 ) ) < ( abs ` ( F ` x ) ) ) )

  disjoint A x
  disjoint x z
  disjoint D x
  disjoint D z
  disjoint N x
  disjoint x y
  disjoint F x
  disjoint y z
  disjoint F y
  disjoint F z
  disjoint J x
  disjoint J z
  disjoint ph x
  disjoint ph y
  disjoint ph z
  disjoint R x
  disjoint R y
  disjoint k n
  disjoint k r
  disjoint k s
  disjoint k x
  disjoint A k
  disjoint n r
  disjoint n s
  disjoint n x
  disjoint A n
  disjoint r s
  disjoint r x
  disjoint A r
  disjoint s x
  disjoint A s
  disjoint s z
  disjoint D s
  disjoint E r
  disjoint K k
  disjoint K n
  disjoint N k
  disjoint N n
  disjoint N r
  disjoint N s
  disjoint k w
  disjoint k y
  disjoint k z
  disjoint F k
  disjoint n w
  disjoint n y
  disjoint n z
  disjoint F n
  disjoint r w
  disjoint r y
  disjoint r z
  disjoint F r
  disjoint s w
  disjoint s y
  disjoint F s
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint F w
  disjoint J s
  disjoint k ph
  disjoint ph s
  disjoint ph w
  disjoint R s
  disjoint S k
  disjoint S s
  disjoint T k
  disjoint T r
  disjoint T x
  disjoint U r
  disjoint U x
  disjoint X k
  disjoint X n
  disjoint X r
  disjoint X s
  disjoint X w
  disjoint X x
  disjoint X y
  disjoint X z
  assert |- ( ph -> E. z e. CC A. x e. CC ( abs ` ( F ` z ) ) <_ ( abs ` ( F ` x ) ) )

  proof
    wph
    vz
    cv
    #
    cF
    cfv
    #
    cabs
    cfv
    #
    vx
    cv
    #
    cF
    cfv
    #
    cabs
    cfv
    #
    cle
    wbr
    #
    vx
    cD
    wral
    #
    vz
    cc
    wrex
    #
    @6
    vx
    cc
    wral
    #
    vz
    cc
    wrex
    cD
    cc
    wss
    #
    wph
    @7
    vz
    cD
    wrex
    #
    @8
    cD
    vy
    cv
    #
    cabs
    cfv
    #
    cR
    cle
    wbr
    #
    vy
    cc
    crab
    #
    cc
    ftalem3.5
    @14
    vy
    cc
    ssrab2
    eqsstri
    #
    wph
    @0
    cabs
    cF
    ccom
    #
    cD
    cres
    #
    cfv
    #
    @3
    @18
    cfv
    #
    cle
    wbr
    #
    vx
    cD
    wral
    #
    vz
    cD
    wrex
    @11
    wph
    vz
    vx
    @18
    cJ
    cD
    crest
    co
    #
    cioo
    crn
    ctg
    cfv
    #
    cD
    cD
    @23
    cJ
    cc
    ctopon
    cfv
    wcel
    @10
    @23
    cD
    ctopon
    cfv
    wcel
    cJ
    ftalem3.6
    cnfldtopon
    #
    @16
    cD
    cJ
    cc
    resttopon
    mp2an
    toponunii
    @24
    eqid
    wph
    cD
    cJ
    ccld
    cfv
    wcel
    #
    @3
    cabs
    cfv
    #
    vs
    cv
    #
    cle
    wbr
    #
    vx
    cD
    wral
    #
    vs
    cr
    wrex
    #
    @23
    ccmp
    wcel
    #
    wph
    cabs
    cmin
    ccom
    #
    cc
    cxmt
    cfv
    wcel
    #
    cc0
    cc
    wcel
    #
    cR
    cxr
    wcel
    @26
    @34
    wph
    cnxmet
    a1i
    @35
    wph
    0cn
    a1i
    #
    wph
    cR
    ftalem3.7
    rpxrd
    vy
    @33
    cc0
    cR
    cD
    cJ
    cc
    cJ
    ftalem3.6
    cnfldtopn
    cD
    @15
    cc0
    @12
    @33
    co
    #
    cR
    cle
    wbr
    #
    vy
    cc
    crab
    ftalem3.5
    @38
    @14
    vy
    cc
    @12
    cc
    wcel
    #
    @37
    @13
    cR
    cle
    @39
    @37
    cc0
    @12
    cmin
    co
    #
    cabs
    cfv
    #
    @13
    @35
    @39
    @37
    @41
    wceq
    0cn
    cc0
    @12
    @33
    @33
    eqid
    cnmetdval
    mpan
    @39
    @41
    @12
    cneg
    #
    cabs
    cfv
    @13
    @42
    @40
    cabs
    @12
    df-neg
    fveq2i
    @12
    absneg
    syl5eqr
    eqtrd
    breq1d
    rabbiia
    eqtr4i
    blcld
    syl3anc
    wph
    cR
    cr
    wcel
    #
    @27
    cR
    cle
    wbr
    #
    vx
    cD
    wral
    #
    @31
    wph
    cR
    ftalem3.7
    rpred
    #
    @44
    vx
    cD
    @3
    cD
    wcel
    #
    @3
    cc
    wcel
    #
    @44
    @14
    @44
    vy
    @3
    cc
    cD
    @12
    @3
    wceq
    @13
    @27
    cR
    cle
    @12
    @3
    cabs
    fveq2
    breq1d
    ftalem3.5
    elrab2
    #
    simprbi
    rgen
    @30
    @45
    vs
    cR
    cr
    @28
    cR
    wceq
    @29
    @44
    vx
    cD
    @28
    cR
    @27
    cle
    breq2
    ralbidv
    rspcev
    sylancl
    @10
    @32
    @26
    @31
    wa
    wb
    @16
    vx
    @23
    cJ
    cD
    vs
    ftalem3.6
    @23
    eqid
    cnheibor
    ax-mp
    sylanbrc
    wph
    @17
    cJ
    @24
    ccn
    co
    #
    wcel
    @10
    @18
    @23
    @24
    ccn
    co
    wcel
    wph
    @17
    cc
    cr
    ccncf
    co
    #
    @50
    wph
    cc
    cc
    cr
    cF
    cabs
    wph
    cF
    cS
    cply
    cfv
    wcel
    #
    cF
    cc
    cc
    ccncf
    co
    wcel
    ftalem.3
    cS
    cF
    plycn
    syl
    cabs
    @51
    wcel
    wph
    abscncf
    a1i
    cncfco
    cc
    cc
    wss
    cr
    cc
    wss
    @51
    @50
    wceq
    cc
    ssid
    ax-resscn
    cc
    cr
    cJ
    cJ
    @24
    ftalem3.6
    cJ
    cc
    crest
    co
    #
    cJ
    cJ
    ctop
    wcel
    @53
    cJ
    wceq
    cJ
    ftalem3.6
    cnfldtop
    cJ
    ctop
    cc
    cc
    cJ
    @25
    toponunii
    #
    restid
    ax-mp
    eqcomi
    cJ
    ftalem3.6
    tgioo2
    cncfcn
    mp2an
    syl6eleq
    @16
    cD
    @17
    cJ
    @24
    cc
    @54
    cnrest
    sylancl
    wph
    cc0
    cD
    wcel
    #
    cD
    c0
    wne
    wph
    @35
    cc0
    cR
    cle
    wbr
    #
    @55
    @36
    wph
    cR
    ftalem3.7
    rpge0d
    @14
    @56
    vy
    cc0
    cc
    cD
    @12
    cc0
    wceq
    #
    @13
    cc0
    cR
    cle
    @57
    @13
    cc0
    cabs
    cfv
    cc0
    @12
    cc0
    cabs
    fveq2
    abs0
    syl6eq
    breq1d
    ftalem3.5
    elrab2
    sylanbrc
    #
    cD
    cc0
    ne0i
    syl
    evth2
    wph
    @22
    @7
    vz
    cD
    wph
    @0
    cD
    wcel
    #
    wa
    #
    @21
    @6
    vx
    cD
    @60
    @47
    wa
    #
    @19
    @2
    @20
    @5
    cle
    @61
    @19
    @0
    @17
    cfv
    #
    @2
    @59
    @19
    @62
    wceq
    wph
    @47
    @0
    cD
    @17
    fvres
    ad2antlr
    @61
    cc
    cc
    cF
    wf
    #
    @0
    cc
    wcel
    #
    @62
    @2
    wceq
    wph
    @63
    @59
    @47
    wph
    @52
    @63
    ftalem.3
    cS
    cF
    plyf
    syl
    #
    ad2antrr
    #
    @61
    cD
    cc
    @0
    @16
    wph
    @59
    @47
    simplr
    sseldi
    cc
    cc
    @0
    cabs
    cF
    fvco3
    syl2anc
    eqtrd
    @61
    @20
    @3
    @17
    cfv
    #
    @5
    @47
    @20
    @67
    wceq
    @60
    @3
    cD
    @17
    fvres
    adantl
    @61
    @63
    @48
    @67
    @5
    wceq
    @66
    @61
    cD
    cc
    @3
    @16
    @60
    @47
    simpr
    sseldi
    cc
    cc
    @3
    cabs
    cF
    fvco3
    syl2anc
    eqtrd
    breq12d
    ralbidva
    rexbidva
    mpbid
    @7
    vz
    cD
    cc
    ssrexv
    mpsyl
    wph
    @7
    @9
    vz
    cc
    wph
    @64
    wa
    #
    @7
    @7
    @6
    vx
    cc
    cD
    cdif
    #
    wral
    #
    wa
    #
    @9
    @68
    @7
    @70
    @68
    @7
    @2
    cc0
    cF
    cfv
    #
    cabs
    cfv
    #
    cle
    wbr
    #
    @70
    @68
    @55
    @7
    @74
    wi
    wph
    @55
    @64
    @58
    adantr
    @6
    @74
    vx
    cc0
    cD
    @3
    cc0
    wceq
    #
    @5
    @73
    @2
    cle
    @75
    @4
    @72
    cabs
    @3
    cc0
    cF
    fveq2
    fveq2d
    breq2d
    rspcv
    syl
    @68
    @74
    @6
    vx
    @69
    @68
    @3
    @69
    wcel
    #
    wa
    #
    @74
    @73
    @5
    cle
    wbr
    #
    @6
    @77
    @73
    @5
    @77
    @72
    @77
    @63
    @35
    @72
    cc
    wcel
    wph
    @63
    @64
    @76
    @65
    ad2antrr
    #
    0cn
    cc
    cc
    cc0
    cF
    ffvelrn
    sylancl
    abscld
    #
    @77
    @4
    @77
    cc
    cc
    @3
    cF
    @79
    @77
    @3
    cc
    cD
    @68
    @76
    simpr
    #
    eldifad
    #
    ffvelrnd
    abscld
    #
    @77
    cR
    @27
    clt
    wbr
    #
    @73
    @5
    clt
    wbr
    #
    wi
    #
    vx
    cc
    wral
    #
    @48
    @84
    @85
    wph
    @87
    @64
    @76
    ftalem3.8
    ad2antrr
    @82
    @77
    @84
    @44
    wn
    @77
    @47
    @44
    @77
    @3
    cc
    cD
    @81
    eldifbd
    @77
    @48
    @47
    @44
    wb
    @82
    @47
    @48
    @44
    @49
    baib
    syl
    mtbid
    @77
    cR
    @27
    wph
    @43
    @64
    @76
    @46
    ad2antrr
    @77
    @3
    @82
    abscld
    ltnled
    mpbird
    @86
    vx
    cc
    rsp
    syl3c
    ltled
    @77
    @2
    cr
    wcel
    @73
    cr
    wcel
    @5
    cr
    wcel
    @74
    @78
    wa
    @6
    wi
    @77
    @1
    @77
    cc
    cc
    @0
    cF
    @79
    wph
    @64
    @76
    simplr
    ffvelrnd
    abscld
    @80
    @83
    @2
    @73
    @5
    letr
    syl3anc
    mpan2d
    ralrimdva
    syld
    ancld
    @71
    @6
    vx
    cD
    @69
    cun
    #
    wral
    @9
    @6
    vx
    cD
    @69
    ralunb
    @6
    vx
    @88
    cc
    @88
    cD
    cc
    cun
    #
    cc
    cD
    cc
    undif2
    @10
    @89
    cc
    wceq
    @16
    cD
    cc
    ssequn1
    mpbi
    eqtri
    raleqi
    bitr3i
    syl6ib
    reximdva
    mpd
end
