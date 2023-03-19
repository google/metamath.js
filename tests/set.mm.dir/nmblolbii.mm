include "wcel.mm"
include "cfv.mm"
include "cmul.mm"
include "co.mm"
include "cle.mm"
include "wbr.mm"
include "cn0v.mm"
include "wceq.mm"
include "fveq2.mm"
include "fveq2d.mm"
include "oveq2d.mm"
include "breq12d.mm"
include "wne.mm"
include "wa.mm"
include "cdiv.mm"
include "c1.mm"
include "cns.mm"
include "cr.mm"
include "cc0.mm"
include "cba.mm"
include "cnv.mm"
include "nvcl.mm"
include "mpan.mm"
include "adantr.mm"
include "wb.mm"
include "eqid.mm"
include "nvz.mm"
include "necon3bid.mm"
include "biimpar.mm"
include "rereccld.mm"
include "clt.mm"
include "nvgt0.mm"
include "biimpa.mm"
include "recgt0d.mm"
include "wi.mm"
include "0re.mm"
include "ltle.mm"
include "sylancr.mm"
include "mpd.mm"
include "wf.mm"
include "blof.mm"
include "mp3an.mm"
include "ffvelrni.mm"
include "nvsge0.mm"
include "mp3an1.mm"
include "syl21anc.mm"
include "cc.mm"
include "recnd.mm"
include "simpl.mm"
include "clno.mm"
include "w3a.mm"
include "bloln.mm"
include "3pm3.2i.mm"
include "lnomul.mm"
include "syl2anc.mm"
include "divrec2d.mm"
include "3eqtr4rd.mm"
include "nvscl.mm"
include "ancoms.mm"
include "syldan.mm"
include "nv1.mm"
include "eqle.mm"
include "nmoolb.mm"
include "eqbrtrd.mm"
include "nmblore.mm"
include "a1i.mm"
include "ledivmul2.mm"
include "syl112anc.mm"
include "mpbid.mm"
include "0le0.mm"
include "lno0.mm"
include "fveq2i.mm"
include "nvz0.mm"
include "ax-mp.mm"
include "eqtri.mm"
include "oveq2i.mm"
include "recni.mm"
include "mul01i.mm"
include "3brtr4i.mm"
include "pm2.61ne.mm"

theorem nmblolbii
  let cA: class A
  let cB: class B
  let cT: class T
  let cU: class U
  let cL: class L
  let cM: class M
  let cN: class N
  let cW: class W
  let cX: class X
  assume nmblolbi.1: |- X = ( BaseSet ` U )
  assume nmblolbi.4: |- L = ( normCV ` U )
  assume nmblolbi.5: |- M = ( normCV ` W )
  assume nmblolbi.6: |- N = ( U normOpOLD W )
  assume nmblolbi.7: |- B = ( U BLnOp W )
  assume nmblolbi.u: |- U e. NrmCVec
  assume nmblolbi.w: |- W e. NrmCVec
  assume nmblolbii.b: |- T e. B


  assert |- ( A e. X -> ( M ` ( T ` A ) ) <_ ( ( N ` T ) x. ( L ` A ) ) )

  proof
    cA
    cX
    wcel
    #
    cA
    cT
    cfv
    #
    cM
    cfv
    #
    cT
    cN
    cfv
    #
    cA
    cL
    cfv
    #
    cmul
    co
    #
    cle
    wbr
    #
    cU
    cn0v
    cfv
    #
    cT
    cfv
    #
    cM
    cfv
    #
    @3
    @7
    cL
    cfv
    #
    cmul
    co
    #
    cle
    wbr
    #
    cA
    @7
    cA
    @7
    wceq
    #
    @2
    @9
    @5
    @11
    cle
    @13
    @1
    @8
    cM
    cA
    @7
    cT
    fveq2
    fveq2d
    @13
    @4
    @10
    @3
    cmul
    cA
    @7
    cL
    fveq2
    oveq2d
    breq12d
    @0
    cA
    @7
    wne
    #
    wa
    #
    @2
    @4
    cdiv
    co
    #
    @3
    cle
    wbr
    #
    @6
    @15
    @16
    c1
    @4
    cdiv
    co
    #
    cA
    cU
    cns
    cfv
    #
    co
    #
    cT
    cfv
    #
    cM
    cfv
    #
    @3
    cle
    @15
    @18
    @1
    cW
    cns
    cfv
    #
    co
    #
    cM
    cfv
    #
    @18
    @2
    cmul
    co
    #
    @22
    @16
    @15
    @18
    cr
    wcel
    #
    cc0
    @18
    cle
    wbr
    #
    @1
    cW
    cba
    cfv
    #
    wcel
    #
    @25
    @26
    wceq
    #
    @15
    @4
    @0
    @4
    cr
    wcel
    #
    @14
    cU
    cnv
    wcel
    #
    @0
    @32
    nmblolbi.u
    cA
    cU
    cL
    cX
    nmblolbi.1
    nmblolbi.4
    nvcl
    mpan
    adantr
    #
    @0
    @4
    cc0
    wne
    @14
    @0
    @4
    cc0
    cA
    @7
    @33
    @0
    @4
    cc0
    wceq
    @13
    wb
    nmblolbi.u
    cA
    cU
    cL
    cX
    @7
    nmblolbi.1
    @7
    eqid
    #
    nmblolbi.4
    nvz
    mpan
    necon3bid
    biimpar
    #
    rereccld
    #
    @15
    cc0
    @18
    clt
    wbr
    #
    @28
    @15
    @4
    @34
    @0
    @14
    cc0
    @4
    clt
    wbr
    #
    @33
    @0
    @14
    @39
    wb
    nmblolbi.u
    cA
    cU
    cL
    cX
    @7
    nmblolbi.1
    @35
    nmblolbi.4
    nvgt0
    mpan
    biimpa
    #
    recgt0d
    @15
    cc0
    cr
    wcel
    @27
    @38
    @28
    wi
    0re
    @37
    cc0
    @18
    ltle
    sylancr
    mpd
    @0
    @30
    @14
    cX
    @29
    cA
    cT
    @33
    cW
    cnv
    wcel
    #
    cT
    cB
    wcel
    #
    cX
    @29
    cT
    wf
    #
    nmblolbi.u
    nmblolbi.w
    nmblolbii.b
    cB
    cT
    cU
    cW
    cX
    @29
    nmblolbi.1
    @29
    eqid
    #
    nmblolbi.7
    blof
    mp3an
    #
    ffvelrni
    #
    adantr
    @41
    @27
    @28
    wa
    @30
    @31
    nmblolbi.w
    @18
    @1
    @23
    cW
    cM
    @29
    @44
    @23
    eqid
    #
    nmblolbi.5
    nvsge0
    mp3an1
    syl21anc
    @15
    @21
    @24
    cM
    @15
    @18
    cc
    wcel
    #
    @0
    @21
    @24
    wceq
    #
    @15
    @18
    @37
    recnd
    #
    @0
    @14
    simpl
    @33
    @41
    cT
    cU
    cW
    clno
    co
    #
    wcel
    #
    w3a
    @48
    @0
    wa
    @49
    @33
    @41
    @52
    nmblolbi.u
    nmblolbi.w
    @33
    @41
    @42
    @52
    nmblolbi.u
    nmblolbi.w
    nmblolbii.b
    cB
    cT
    cU
    @51
    cW
    @51
    eqid
    #
    nmblolbi.7
    bloln
    mp3an
    #
    3pm3.2i
    @18
    cA
    @19
    @23
    cT
    cU
    @51
    cW
    cX
    nmblolbi.1
    @19
    eqid
    #
    @47
    @53
    lnomul
    mpan
    syl2anc
    fveq2d
    @15
    @2
    @4
    @15
    @2
    @0
    @2
    cr
    wcel
    #
    @14
    @0
    @41
    @30
    @56
    nmblolbi.w
    @46
    @1
    cW
    cM
    @29
    @44
    nmblolbi.5
    nvcl
    sylancr
    adantr
    #
    recnd
    @15
    @4
    @34
    recnd
    @36
    divrec2d
    3eqtr4rd
    @15
    @20
    cX
    wcel
    #
    @20
    cL
    cfv
    #
    c1
    cle
    wbr
    #
    @22
    @3
    cle
    wbr
    #
    @0
    @14
    @48
    @58
    @50
    @48
    @0
    @58
    @33
    @48
    @0
    @58
    nmblolbi.u
    @18
    cA
    @19
    cU
    cX
    nmblolbi.1
    @55
    nvscl
    mp3an1
    ancoms
    syldan
    #
    @15
    @59
    cr
    wcel
    #
    @59
    c1
    wceq
    #
    @60
    @15
    @33
    @58
    @63
    nmblolbi.u
    @62
    @20
    cU
    cL
    cX
    nmblolbi.1
    nmblolbi.4
    nvcl
    sylancr
    @33
    @0
    @14
    @64
    nmblolbi.u
    cA
    @19
    cU
    cL
    cX
    @7
    nmblolbi.1
    @55
    @35
    nmblolbi.4
    nv1
    mp3an1
    @59
    c1
    eqle
    syl2anc
    @33
    @41
    @43
    w3a
    @58
    @60
    wa
    @61
    @33
    @41
    @43
    nmblolbi.u
    nmblolbi.w
    @45
    3pm3.2i
    @20
    cT
    cU
    cL
    cM
    cN
    cW
    cX
    @29
    nmblolbi.1
    @44
    nmblolbi.4
    nmblolbi.5
    nmblolbi.6
    nmoolb
    mpan
    syl2anc
    eqbrtrd
    @15
    @56
    @3
    cr
    wcel
    #
    @32
    @39
    @17
    @6
    wb
    @57
    @65
    @15
    @33
    @41
    @42
    @65
    nmblolbi.u
    nmblolbi.w
    nmblolbii.b
    cB
    cT
    cU
    cN
    cW
    cX
    @29
    nmblolbi.1
    @44
    nmblolbi.6
    nmblolbi.7
    nmblore
    mp3an
    #
    a1i
    @34
    @40
    @2
    @3
    @4
    ledivmul2
    syl112anc
    mpbid
    @12
    @0
    cc0
    cc0
    @9
    @11
    cle
    0le0
    @9
    cW
    cn0v
    cfv
    #
    cM
    cfv
    #
    cc0
    @8
    @67
    cM
    @33
    @41
    @52
    @8
    @67
    wceq
    nmblolbi.u
    nmblolbi.w
    @54
    @7
    cT
    cU
    @51
    cW
    cX
    @29
    @67
    nmblolbi.1
    @44
    @35
    @67
    eqid
    #
    @53
    lno0
    mp3an
    fveq2i
    @41
    @68
    cc0
    wceq
    nmblolbi.w
    cW
    cM
    @67
    @69
    nmblolbi.5
    nvz0
    ax-mp
    eqtri
    @11
    @3
    cc0
    cmul
    co
    cc0
    @10
    cc0
    @3
    cmul
    @33
    @10
    cc0
    wceq
    nmblolbi.u
    cU
    cL
    @7
    @35
    nmblolbi.4
    nvz0
    ax-mp
    oveq2i
    @3
    @3
    @66
    recni
    mul01i
    eqtri
    3brtr4i
    a1i
    pm2.61ne
end
