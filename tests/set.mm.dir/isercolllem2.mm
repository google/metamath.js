include "c1.mm"
include "cfv.mm"
include "cuz.mm"
include "wcel.mm"
include "wa.mm"
include "ccnv.mm"
include "cfz.mm"
include "co.mm"
include "cima.mm"
include "cr.mm"
include "clt.mm"
include "csup.mm"
include "chash.mm"
include "cv.mm"
include "cn.mm"
include "wi.mm"
include "elfznn.mm"
include "a1i.mm"
include "cdm.mm"
include "cnvimass.mm"
include "wf.mm"
include "wceq.mm"
include "adantr.mm"
include "fdm.mm"
include "syl.mm"
include "syl5sseq.mm"
include "sseld.mm"
include "wb.mm"
include "cle.mm"
include "wbr.mm"
include "cz.mm"
include "id.mm"
include "nnuz.mm"
include "syl6eleq.mm"
include "wor.mm"
include "cfn.mm"
include "c0.mm"
include "wne.mm"
include "wss.mm"
include "ltso.mm"
include "cen.mm"
include "fzfid.mm"
include "crn.mm"
include "cin.mm"
include "wfun.mm"
include "ffun.mm"
include "funimacnv.mm"
include "3syl.mm"
include "inss1.mm"
include "syl6eqss.mm"
include "ssfi.mm"
include "syl2anc.mm"
include "wf1.mm"
include "cvv.mm"
include "wiso.mm"
include "wf1o.mm"
include "cres.mm"
include "ssid.mm"
include "isercolllem1.mm"
include "mpan2.mm"
include "wfn.mm"
include "ffn.mm"
include "fnresdm.mm"
include "isoeq1.mm"
include "4syl.mm"
include "mpbid.mm"
include "isof1o.mm"
include "f1ocnv.mm"
include "f1ofun.mm"
include "df-f1.mm"
include "sylanbrc.mm"
include "nnex.mm"
include "ssexg.mm"
include "sylancl.mm"
include "f1imaeng.mm"
include "syl3anc.mm"
include "ensymd.mm"
include "enfii.mm"
include "1nn.mm"
include "ffvelrn.mm"
include "simpr.mm"
include "elfzuzb.mm"
include "elpreima.mm"
include "mpbir2and.mm"
include "ne0i.mm"
include "nnssre.mm"
include "syl6ss.mm"
include "fisupcl.mm"
include "syl13anc.mm"
include "sseldd.mm"
include "nnzd.mm"
include "elfz5.mm"
include "syl2anr.mm"
include "simprd.mm"
include "elfzle2.mm"
include "uzssz.mm"
include "eqsstri.mm"
include "zssre.mm"
include "sstri.mm"
include "ffvelrnda.mm"
include "sseldi.mm"
include "ffvelrnd.mm"
include "eluzelz.mm"
include "ad2antlr.mm"
include "letr.mm"
include "mpan2d.mm"
include "cxr.mm"
include "ad2antrr.mm"
include "ressxr.mm"
include "imassrn.mm"
include "frn.mm"
include "syl5ss.mm"
include "leisorel.mm"
include "syl122anc.mm"
include "3imtr4d.mm"
include "baibd.mm"
include "sylan.mm"
include "sylibrd.mm"
include "wral.mm"
include "wrex.mm"
include "fimaxre2.mm"
include "w3a.mm"
include "suprub.mm"
include "ex.mm"
include "impbid.mm"
include "bitrd.mm"
include "pm5.21ndd.mm"
include "eqrdv.mm"
include "fveq2d.mm"
include "cn0.mm"
include "nnnn0d.mm"
include "hashfz1.mm"
include "hashen.mm"
include "mpbird.mm"
include "3eqtr3d.mm"
include "oveq2d.mm"
include "eqtr3d.mm"

theorem isercolllem2
  let wph: wff ph
  let vk: setvar k
  let cG: class G
  let cM: class M
  let cN: class N
  let cZ: class Z
  let vj: setvar j
  let vm: setvar m
  let vn: setvar n
  let vx: setvar x
  let cA: class A
  let cF: class F
  let vy: setvar y
  let cH: class H
  let cS: class S
  assume isercoll.z: |- Z = ( ZZ>= ` M )
  assume isercoll.m: |- ( ph -> M e. ZZ )
  assume isercoll.g: |- ( ph -> G : NN --> Z )
  assume isercoll.i: |- ( ( ph /\ k e. NN ) -> ( G ` k ) < ( G ` ( k + 1 ) ) )

  disjoint N k
  disjoint k ph
  disjoint G k
  disjoint M k
  disjoint j k
  disjoint j m
  disjoint j n
  disjoint j x
  disjoint A j
  disjoint k m
  disjoint k n
  disjoint k x
  disjoint A k
  disjoint m n
  disjoint m x
  disjoint A m
  disjoint n x
  disjoint A n
  disjoint A x
  disjoint F j
  disjoint F k
  disjoint F m
  disjoint F n
  disjoint F x
  disjoint k y
  disjoint n y
  disjoint N n
  disjoint x y
  disjoint N x
  disjoint N y
  disjoint j y
  disjoint j ph
  disjoint m y
  disjoint m ph
  disjoint n ph
  disjoint ph x
  disjoint ph y
  disjoint G j
  disjoint G m
  disjoint G n
  disjoint G x
  disjoint G y
  disjoint H j
  disjoint H k
  disjoint H m
  disjoint H n
  disjoint H x
  disjoint M j
  disjoint M m
  disjoint M n
  disjoint M x
  disjoint M y
  disjoint S x
  disjoint S y
  disjoint Z n
  assert |- ( ( ph /\ N e. ( ZZ>= ` ( G ` 1 ) ) ) -> ( 1 ... ( # ` ( G " ( `' G " ( M ... N ) ) ) ) ) = ( `' G " ( M ... N ) ) )

  proof
    wph
    cN
    c1
    cG
    cfv
    #
    cuz
    cfv
    wcel
    #
    wa
    #
    c1
    cG
    ccnv
    #
    cM
    cN
    cfz
    co
    #
    cima
    #
    cr
    clt
    csup
    #
    cfz
    co
    #
    c1
    cG
    @5
    cima
    #
    chash
    cfv
    #
    cfz
    co
    @5
    @2
    @6
    @9
    c1
    cfz
    @2
    @7
    chash
    cfv
    #
    @5
    chash
    cfv
    #
    @6
    @9
    @2
    @7
    @5
    chash
    @2
    vx
    @7
    @5
    @2
    vx
    cv
    #
    cn
    wcel
    #
    @12
    @7
    wcel
    #
    @12
    @5
    wcel
    #
    @14
    @13
    wi
    @2
    @12
    @6
    elfznn
    a1i
    @2
    @5
    cn
    @12
    @2
    cG
    cdm
    #
    @5
    cn
    cG
    @4
    cnvimass
    @2
    cn
    cZ
    cG
    wf
    #
    @16
    cn
    wceq
    wph
    @17
    @1
    isercoll.g
    adantr
    #
    cn
    cZ
    cG
    fdm
    syl
    syl5sseq
    #
    sseld
    @2
    @13
    @14
    @15
    wb
    @2
    @13
    wa
    #
    @14
    @12
    @6
    cle
    wbr
    #
    @15
    @13
    @12
    c1
    cuz
    cfv
    #
    wcel
    @6
    cz
    wcel
    @14
    @21
    wb
    @2
    @13
    @12
    cn
    @22
    @13
    id
    nnuz
    syl6eleq
    @2
    @6
    @2
    @5
    cn
    @6
    @19
    @2
    cr
    clt
    wor
    #
    @5
    cfn
    wcel
    #
    @5
    c0
    wne
    #
    @5
    cr
    wss
    #
    @6
    @5
    wcel
    #
    @23
    @2
    ltso
    a1i
    @2
    @8
    cfn
    wcel
    #
    @5
    @8
    cen
    wbr
    #
    @24
    @2
    @4
    cfn
    wcel
    @8
    @4
    wss
    @28
    @2
    cM
    cN
    fzfid
    @2
    @8
    @4
    cG
    crn
    #
    cin
    #
    @4
    @2
    @17
    cG
    wfun
    @8
    @31
    wceq
    @18
    cn
    cZ
    cG
    ffun
    @4
    cG
    funimacnv
    3syl
    @4
    @30
    inss1
    syl6eqss
    @4
    @8
    ssfi
    syl2anc
    #
    @2
    @8
    @5
    @2
    cn
    cZ
    cG
    wf1
    #
    @5
    cn
    wss
    #
    @5
    cvv
    wcel
    #
    @8
    @5
    cen
    wbr
    wph
    @33
    @1
    wph
    @17
    @3
    wfun
    #
    @33
    isercoll.g
    wph
    cn
    cG
    cn
    cima
    #
    clt
    clt
    cG
    wiso
    #
    cn
    @37
    cG
    wf1o
    @37
    cn
    @3
    wf1o
    @36
    wph
    cn
    @37
    clt
    clt
    cG
    cn
    cres
    #
    wiso
    #
    @38
    wph
    cn
    cn
    wss
    @40
    cn
    ssid
    wph
    cn
    vk
    cG
    cM
    cZ
    isercoll.z
    isercoll.m
    isercoll.g
    isercoll.i
    isercolllem1
    mpan2
    wph
    @17
    cG
    cn
    wfn
    #
    @39
    cG
    wceq
    @40
    @38
    wb
    isercoll.g
    cn
    cZ
    cG
    ffn
    #
    cn
    cG
    fnresdm
    cn
    @37
    clt
    clt
    cG
    @39
    isoeq1
    4syl
    mpbid
    #
    cn
    @37
    clt
    clt
    cG
    isof1o
    cn
    @37
    cG
    f1ocnv
    @37
    cn
    @3
    f1ofun
    4syl
    cn
    cZ
    cG
    df-f1
    sylanbrc
    adantr
    @19
    @2
    @34
    cn
    cvv
    wcel
    @35
    @19
    nnex
    @5
    cn
    cvv
    ssexg
    sylancl
    cn
    cZ
    @5
    cG
    cvv
    f1imaeng
    syl3anc
    ensymd
    #
    @5
    @8
    enfii
    syl2anc
    #
    @2
    c1
    @5
    wcel
    #
    @25
    @2
    @46
    c1
    cn
    wcel
    #
    @0
    @4
    wcel
    #
    @47
    @2
    1nn
    a1i
    @2
    @0
    cM
    cuz
    cfv
    #
    wcel
    #
    @1
    @48
    wph
    @50
    @1
    wph
    @0
    cZ
    @49
    wph
    @17
    @47
    @0
    cZ
    wcel
    isercoll.g
    1nn
    cn
    cZ
    c1
    cG
    ffvelrn
    sylancl
    isercoll.z
    syl6eleq
    adantr
    wph
    @1
    simpr
    @0
    cM
    cN
    elfzuzb
    sylanbrc
    @2
    @41
    @46
    @47
    @48
    wa
    wb
    @2
    @17
    @41
    @18
    @42
    syl
    #
    cn
    c1
    @4
    cG
    elpreima
    syl
    mpbir2and
    @5
    c1
    ne0i
    syl
    #
    @2
    @5
    cn
    cr
    @19
    nnssre
    syl6ss
    #
    cr
    @5
    clt
    fisupcl
    syl13anc
    #
    sseldd
    #
    nnzd
    @12
    c1
    @6
    elfz5
    syl2anr
    @20
    @21
    @15
    @20
    @21
    @12
    cG
    cfv
    #
    @4
    wcel
    #
    @15
    @20
    @56
    @6
    cG
    cfv
    #
    cle
    wbr
    #
    @56
    cN
    cle
    wbr
    #
    @21
    @57
    @20
    @59
    @58
    cN
    cle
    wbr
    #
    @60
    @2
    @61
    @13
    @2
    @58
    @4
    wcel
    #
    @61
    @2
    @6
    cn
    wcel
    #
    @62
    @2
    @27
    @63
    @62
    wa
    #
    @54
    @2
    @41
    @27
    @64
    wb
    @51
    cn
    @6
    @4
    cG
    elpreima
    syl
    mpbid
    simprd
    @58
    cM
    cN
    elfzle2
    syl
    adantr
    @20
    @56
    cr
    wcel
    @58
    cr
    wcel
    cN
    cr
    wcel
    @59
    @61
    wa
    @60
    wi
    @20
    cZ
    cr
    @56
    cZ
    cz
    cr
    cZ
    @49
    cz
    isercoll.z
    cM
    uzssz
    eqsstri
    zssre
    sstri
    #
    @2
    cn
    cZ
    @12
    cG
    @18
    ffvelrnda
    #
    sseldi
    @20
    cZ
    cr
    @58
    @65
    @2
    @58
    cZ
    wcel
    @13
    @2
    cn
    cZ
    @6
    cG
    @18
    @55
    ffvelrnd
    adantr
    sseldi
    @20
    cz
    cr
    cN
    zssre
    @1
    cN
    cz
    wcel
    #
    wph
    @13
    @0
    cN
    eluzelz
    ad2antlr
    #
    sseldi
    @56
    @58
    cN
    letr
    syl3anc
    mpan2d
    @20
    @38
    cn
    cxr
    wss
    @37
    cxr
    wss
    @13
    @63
    @21
    @59
    wb
    wph
    @38
    @1
    @13
    @43
    ad2antrr
    @20
    cn
    cr
    cxr
    cn
    cr
    wss
    @20
    nnssre
    a1i
    ressxr
    syl6ss
    @20
    @37
    cr
    cxr
    @20
    @37
    cZ
    cr
    @20
    @37
    @30
    cZ
    cG
    cn
    imassrn
    @20
    @17
    @30
    cZ
    wss
    wph
    @17
    @1
    @13
    isercoll.g
    ad2antrr
    cn
    cZ
    cG
    frn
    syl
    syl5ss
    @65
    syl6ss
    ressxr
    syl6ss
    @2
    @13
    simpr
    @2
    @63
    @13
    @55
    adantr
    cn
    @37
    @12
    @6
    cG
    leisorel
    syl122anc
    @20
    @56
    @49
    wcel
    @67
    @57
    @60
    wb
    @20
    @56
    cZ
    @49
    @66
    isercoll.z
    syl6eleq
    @68
    @56
    cM
    cN
    elfz5
    syl2anc
    3imtr4d
    @2
    @41
    @13
    @15
    @57
    wb
    @51
    @41
    @15
    @13
    @57
    cn
    @12
    @4
    cG
    elpreima
    baibd
    sylan
    sylibrd
    @2
    @15
    @21
    wi
    #
    @13
    @2
    @26
    @25
    vy
    cv
    @12
    cle
    wbr
    vy
    @5
    wral
    vx
    cr
    wrex
    #
    @69
    @53
    @52
    @2
    @26
    @24
    @70
    @53
    @45
    vx
    vy
    @5
    fimaxre2
    syl2anc
    @26
    @25
    @70
    w3a
    @15
    @21
    vx
    vy
    @5
    @12
    suprub
    ex
    syl3anc
    adantr
    impbid
    bitrd
    ex
    pm5.21ndd
    eqrdv
    #
    fveq2d
    @2
    @6
    cn0
    wcel
    @10
    @6
    wceq
    @2
    @6
    @55
    nnnn0d
    @6
    hashfz1
    syl
    @2
    @11
    @9
    wceq
    #
    @29
    @44
    @2
    @24
    @28
    @72
    @29
    wb
    @45
    @32
    @5
    @8
    hashen
    syl2anc
    mpbird
    3eqtr3d
    oveq2d
    @71
    eqtr3d
end
