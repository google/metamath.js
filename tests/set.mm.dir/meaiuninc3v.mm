include "cv.mm"
include "cfv.mm"
include "cle.mm"
include "wbr.mm"
include "wral.mm"
include "cr.mm"
include "wrex.mm"
include "ciun.mm"
include "clsxlim.mm"
include "wa.mm"
include "cz.mm"
include "wcel.mm"
include "adantr.mm"
include "cxr.mm"
include "wf.mm"
include "cdm.mm"
include "cmea.mm"
include "eqid.mm"
include "ffvelrnda.mm"
include "meaxrcl.mm"
include "fmptd.mm"
include "nfv.mm"
include "nfcv.mm"
include "nfra1.mm"
include "nfrex.mm"
include "nfan.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "wss.mm"
include "adantlr.mm"
include "simpr.mm"
include "meaiunincf.mm"
include "climxlim2.mm"
include "wn.mm"
include "clt.mm"
include "wb.mm"
include "wceq.mm"
include "fveq2.mm"
include "fveq2d.mm"
include "breq2d.mm"
include "cbvrexv.mm"
include "a1i.mm"
include "rexr.mm"
include "ad2antlr.mm"
include "xrltnled.mm"
include "rexbidva.mm"
include "bitrd.mm"
include "ralbidva.mm"
include "rexnal.mm"
include "ralbii.mm"
include "ralnex.mm"
include "bitri.mm"
include "mpbird.mm"
include "syldan.mm"
include "cpnf.mm"
include "cuz.mm"
include "simp-4r.mm"
include "syl.mm"
include "simp-4l.mm"
include "uztrn2.mm"
include "ad4ant24.mm"
include "syl2anc.mm"
include "wi.mm"
include "eleq1w.mm"
include "anbi2d.mm"
include "eleq1d.mm"
include "imbi12d.mm"
include "chvarv.mm"
include "ad5ant13.mm"
include "simplr.mm"
include "w3a.mm"
include "3ad2ant1.mm"
include "3adant3.mm"
include "simp1.mm"
include "3adant1.mm"
include "simp3.mm"
include "cfzo.mm"
include "simpll.mm"
include "uzssd3.mm"
include "elfzouz.mm"
include "adantl.mm"
include "sseldd.mm"
include "adantll.mm"
include "oveq1.mm"
include "sseq12d.mm"
include "3adantl3.mm"
include "ssinc.mm"
include "meassle.mm"
include "cvv.mm"
include "fvexd.mm"
include "fvmpt2.mm"
include "breqtrrd.mm"
include "ad5ant135.mm"
include "xrltletrd.mm"
include "xrltled.mm"
include "ralrimiva.mm"
include "ex.mm"
include "reximdva.mm"
include "ralimdva.mm"
include "imp.mm"
include "cmpt.mm"
include "nfmpt1.mm"
include "nfcxfr.mm"
include "xlimpnf.mm"
include "rspa.mm"
include "nfre1.mm"
include "nfral.mm"
include "ad3antlr.mm"
include "dmmeasal.mm"
include "com.mm"
include "cdom.mm"
include "uzct.mm"
include "saliuncl.mm"
include "ad3antrrr.mm"
include "ad4ant13.mm"
include "ssiun2s.mm"
include "exp31.mm"
include "rexlimd.mm"
include "mpd.mm"
include "ralrimia.mm"
include "xrpnf.mm"
include "pm2.61dan.mm"

theorem meaiuninc3v
  let wph: wff ph
  let cS: class S
  let vn: setvar n
  let cE: class E
  let cM: class M
  let cN: class N
  let cZ: class Z
  let vj: setvar j
  let vk: setvar k
  let vx: setvar x
  assume meaiuninc3v.m: |- ( ph -> M e. Meas )
  assume meaiuninc3v.n: |- ( ph -> N e. ZZ )
  assume meaiuninc3v.z: |- Z = ( ZZ>= ` N )
  assume meaiuninc3v.e: |- ( ph -> E : Z --> dom M )
  assume meaiuninc3v.i: |- ( ( ph /\ n e. Z ) -> ( E ` n ) C_ ( E ` ( n + 1 ) ) )
  assume meaiuninc3v.s: |- S = ( n e. Z |-> ( M ` ( E ` n ) ) )

  disjoint E n
  disjoint M n
  disjoint Z n
  disjoint n ph
  disjoint E j
  disjoint E k
  disjoint j k
  disjoint j n
  disjoint k n
  disjoint E x
  disjoint j x
  disjoint n x
  disjoint M j
  disjoint M x
  disjoint S j
  disjoint S x
  disjoint Z j
  disjoint Z k
  disjoint Z x
  disjoint j ph
  disjoint k ph
  disjoint ph x
  disjoint k x
  assert |- ( ph -> S ~~>* ( M ` U_ n e. Z ( E ` n ) ) )

  proof
    wph
    vn
    cv
    #
    cE
    cfv
    #
    cM
    cfv
    #
    vx
    cv
    #
    cle
    wbr
    #
    vn
    cZ
    wral
    #
    vx
    cr
    wrex
    #
    cS
    vn
    cZ
    @1
    ciun
    #
    cM
    cfv
    #
    clsxlim
    wbr
    #
    wph
    @6
    wa
    #
    @8
    cS
    cN
    cZ
    wph
    cN
    cz
    wcel
    @6
    meaiuninc3v.n
    adantr
    #
    meaiuninc3v.z
    wph
    cZ
    cxr
    cS
    wf
    @6
    wph
    vn
    cZ
    @2
    cxr
    cS
    wph
    @0
    cZ
    wcel
    #
    wa
    #
    @1
    cM
    cdm
    #
    cM
    wph
    cM
    cmea
    wcel
    #
    @12
    meaiuninc3v.m
    adantr
    @14
    eqid
    #
    wph
    cZ
    @14
    @0
    cE
    meaiuninc3v.e
    ffvelrnda
    #
    meaxrcl
    #
    meaiuninc3v.s
    fmptd
    #
    adantr
    @10
    vx
    cS
    vn
    cE
    cM
    cN
    cZ
    wph
    @6
    vn
    wph
    vn
    nfv
    @5
    vn
    vx
    cr
    vn
    cr
    nfcv
    @4
    vn
    cZ
    nfra1
    nfrex
    nfan
    vn
    cE
    nfcv
    wph
    @15
    @6
    meaiuninc3v.m
    adantr
    @11
    meaiuninc3v.z
    wph
    cZ
    @14
    cE
    wf
    @6
    meaiuninc3v.e
    adantr
    wph
    @12
    @1
    @0
    c1
    caddc
    co
    #
    cE
    cfv
    #
    wss
    #
    @6
    meaiuninc3v.i
    adantlr
    wph
    @6
    simpr
    meaiuninc3v.s
    meaiunincf
    climxlim2
    wph
    @6
    wn
    #
    @3
    vj
    cv
    #
    cE
    cfv
    #
    cM
    cfv
    #
    clt
    wbr
    #
    vj
    cZ
    wrex
    #
    vx
    cr
    wral
    #
    @9
    wph
    @23
    @29
    @29
    wph
    @23
    wa
    @29
    @23
    wph
    @23
    simpr
    wph
    @29
    @23
    wb
    @23
    wph
    @29
    @4
    wn
    #
    vn
    cZ
    wrex
    #
    vx
    cr
    wral
    #
    @23
    wph
    @28
    @31
    vx
    cr
    wph
    @3
    cr
    wcel
    #
    wa
    #
    @28
    @3
    @2
    clt
    wbr
    #
    vn
    cZ
    wrex
    #
    @31
    @28
    @36
    wb
    @34
    @27
    @35
    vj
    vn
    cZ
    @24
    @0
    wceq
    #
    @26
    @2
    @3
    clt
    @37
    @25
    @1
    cM
    @24
    @0
    cE
    fveq2
    fveq2d
    breq2d
    cbvrexv
    a1i
    @34
    @35
    @30
    vn
    cZ
    @34
    @12
    wa
    @3
    @2
    @33
    @3
    cxr
    wcel
    #
    wph
    @12
    @3
    rexr
    #
    ad2antlr
    wph
    @12
    @2
    cxr
    wcel
    #
    @33
    @18
    adantlr
    xrltnled
    rexbidva
    bitrd
    ralbidva
    @32
    @23
    wb
    wph
    @32
    @5
    wn
    #
    vx
    cr
    wral
    @23
    @31
    @41
    vx
    cr
    @4
    vn
    cZ
    rexnal
    ralbii
    @5
    vx
    cr
    ralnex
    bitri
    a1i
    bitrd
    adantr
    mpbird
    wph
    @29
    simpr
    syldan
    wph
    @29
    wa
    #
    cS
    cpnf
    @8
    clsxlim
    @42
    cS
    cpnf
    clsxlim
    wbr
    #
    @3
    @0
    cS
    cfv
    #
    cle
    wbr
    #
    vn
    @24
    cuz
    cfv
    #
    wral
    #
    vj
    cZ
    wrex
    #
    vx
    cr
    wral
    #
    wph
    @29
    @49
    wph
    @28
    @48
    vx
    cr
    @34
    @27
    @47
    vj
    cZ
    @34
    @24
    cZ
    wcel
    #
    wa
    #
    @27
    @47
    @51
    @27
    wa
    #
    @45
    vn
    @46
    @52
    @0
    @46
    wcel
    #
    wa
    #
    @3
    @44
    @54
    @33
    @38
    wph
    @33
    @50
    @27
    @53
    simp-4r
    @39
    syl
    #
    @54
    wph
    @12
    @44
    cxr
    wcel
    wph
    @33
    @50
    @27
    @53
    simp-4l
    @50
    @53
    @12
    @34
    @27
    cN
    @0
    @24
    cZ
    meaiuninc3v.z
    uztrn2
    #
    ad4ant24
    wph
    cZ
    cxr
    @0
    cS
    @19
    ffvelrnda
    syl2anc
    #
    @54
    @3
    @26
    @44
    @55
    wph
    @50
    @26
    cxr
    wcel
    #
    @33
    @27
    @53
    @13
    @40
    wi
    wph
    @50
    wa
    #
    @58
    wi
    vn
    vj
    @0
    @24
    wceq
    #
    @13
    @59
    @40
    @58
    @60
    @12
    @50
    wph
    vn
    vj
    cZ
    eleq1w
    anbi2d
    @60
    @2
    @26
    cxr
    @60
    @1
    @25
    cM
    @0
    @24
    cE
    fveq2
    #
    fveq2d
    eleq1d
    imbi12d
    @18
    chvarv
    #
    ad5ant13
    @57
    @51
    @27
    @53
    simplr
    wph
    @50
    @53
    @26
    @44
    cle
    wbr
    @33
    @27
    wph
    @50
    @53
    w3a
    #
    @26
    @2
    @44
    cle
    @63
    @25
    @1
    @14
    cM
    wph
    @50
    @15
    @53
    meaiuninc3v.m
    3ad2ant1
    @16
    wph
    @50
    @25
    @14
    wcel
    @53
    wph
    cZ
    @14
    @24
    cE
    meaiuninc3v.e
    ffvelrnda
    #
    3adant3
    @63
    wph
    @12
    @1
    @14
    wcel
    wph
    @50
    @53
    simp1
    @50
    @53
    @12
    wph
    @56
    3adant1
    @17
    syl2anc
    @63
    vk
    cE
    @24
    @0
    wph
    @50
    @53
    simp3
    wph
    @50
    vk
    cv
    #
    @24
    @0
    cfzo
    co
    wcel
    #
    @65
    cE
    cfv
    #
    @65
    c1
    caddc
    co
    #
    cE
    cfv
    #
    wss
    #
    @53
    @59
    @66
    wa
    wph
    @65
    cZ
    wcel
    #
    @70
    wph
    @50
    @66
    simpll
    @50
    @66
    @71
    wph
    @50
    @66
    wa
    @46
    cZ
    @65
    @50
    @46
    cZ
    wss
    @66
    cN
    @24
    cZ
    meaiuninc3v.z
    uzssd3
    adantr
    @66
    @65
    @46
    wcel
    @50
    @65
    @24
    @0
    elfzouz
    adantl
    sseldd
    adantll
    @13
    @22
    wi
    wph
    @71
    wa
    #
    @70
    wi
    vn
    vk
    @0
    @65
    wceq
    #
    @13
    @72
    @22
    @70
    @73
    @12
    @71
    wph
    vn
    vk
    cZ
    eleq1w
    anbi2d
    @73
    @1
    @67
    @21
    @69
    @0
    @65
    cE
    fveq2
    @73
    @20
    @68
    cE
    @0
    @65
    c1
    caddc
    oveq1
    fveq2d
    sseq12d
    imbi12d
    meaiuninc3v.i
    chvarv
    syl2anc
    3adantl3
    ssinc
    meassle
    @50
    @53
    @44
    @2
    wceq
    #
    wph
    @50
    @53
    wa
    #
    @12
    @2
    cvv
    wcel
    @74
    @56
    @75
    @1
    cM
    fvexd
    vn
    cZ
    @2
    cvv
    cS
    meaiuninc3v.s
    fvmpt2
    syl2anc
    3adant1
    breqtrrd
    ad5ant135
    xrltletrd
    xrltled
    ralrimiva
    ex
    reximdva
    ralimdva
    imp
    wph
    @43
    @49
    wb
    @29
    wph
    vx
    vj
    vn
    cS
    cN
    cZ
    vn
    cS
    vn
    cZ
    @2
    cmpt
    meaiuninc3v.s
    vn
    cZ
    @2
    nfmpt1
    nfcxfr
    meaiuninc3v.n
    meaiuninc3v.z
    @19
    xlimpnf
    adantr
    mpbird
    @42
    @8
    cpnf
    wceq
    #
    @3
    @8
    cle
    wbr
    #
    vx
    cr
    wral
    #
    @42
    @77
    vx
    cr
    wph
    @29
    vx
    wph
    vx
    nfv
    @28
    vx
    cr
    nfra1
    nfan
    @42
    @33
    wa
    #
    @28
    @77
    @29
    @33
    @28
    wph
    @28
    vx
    cr
    rspa
    adantll
    @79
    @27
    @77
    vj
    cZ
    @42
    @33
    vj
    wph
    @29
    vj
    wph
    vj
    nfv
    @28
    vj
    vx
    cr
    vj
    cr
    nfcv
    @27
    vj
    cZ
    nfre1
    nfral
    nfan
    @33
    vj
    nfv
    nfan
    @77
    vj
    nfv
    wph
    @33
    @50
    @27
    @77
    wi
    wi
    @29
    @34
    @50
    @27
    @77
    @52
    @3
    @8
    @33
    @38
    wph
    @50
    @27
    @39
    ad3antlr
    #
    wph
    @8
    cxr
    wcel
    #
    @33
    @50
    @27
    wph
    @7
    @14
    cM
    meaiuninc3v.m
    @16
    wph
    @14
    vn
    @1
    cZ
    wph
    @14
    cM
    meaiuninc3v.m
    @16
    dmmeasal
    cZ
    com
    cdom
    wbr
    wph
    cN
    cZ
    meaiuninc3v.z
    uzct
    a1i
    @17
    saliuncl
    #
    meaxrcl
    #
    ad3antrrr
    #
    @52
    @3
    @26
    @8
    @80
    wph
    @50
    @58
    @33
    @27
    @62
    ad4ant13
    @84
    @51
    @27
    simpr
    wph
    @50
    @26
    @8
    cle
    wbr
    @33
    @27
    @59
    @25
    @7
    @14
    cM
    wph
    @15
    @50
    meaiuninc3v.m
    adantr
    @16
    @64
    wph
    @7
    @14
    wcel
    @50
    @82
    adantr
    @50
    @25
    @7
    wss
    wph
    vn
    cZ
    @1
    @24
    @25
    @61
    ssiun2s
    adantl
    meassle
    ad4ant13
    xrltletrd
    xrltled
    exp31
    adantlr
    rexlimd
    mpd
    ralrimia
    wph
    @76
    @78
    wb
    #
    @29
    wph
    @81
    @85
    @83
    vx
    @8
    xrpnf
    syl
    adantr
    mpbird
    breqtrrd
    syldan
    pm2.61dan
end
