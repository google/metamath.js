include "cn.mm"
include "wss.mm"
include "wa.mm"
include "cima.mm"
include "clt.mm"
include "cres.mm"
include "wiso.mm"
include "cv.mm"
include "wbr.mm"
include "cfv.mm"
include "wi.mm"
include "wral.mm"
include "wcel.mm"
include "cmin.mm"
include "co.mm"
include "cr.mm"
include "cz.mm"
include "cuz.mm"
include "uzssz.mm"
include "eqsstri.mm"
include "zssre.mm"
include "sstri.mm"
include "wf.mm"
include "ad2antrr.mm"
include "simplrl.mm"
include "ffvelrnd.mm"
include "sseldi.mm"
include "simplrr.mm"
include "nnred.mm"
include "resubcld.mm"
include "simpr.mm"
include "ltsub2dd.mm"
include "cmpt.mm"
include "cle.mm"
include "nnzd.mm"
include "ltled.mm"
include "eluz2.mm"
include "syl3anbrc.mm"
include "cfz.mm"
include "elfzuz.mm"
include "eluznn.mm"
include "sylan.mm"
include "wceq.mm"
include "weq.mm"
include "fveq2.mm"
include "id.mm"
include "oveq12d.mm"
include "eqid.mm"
include "ovex.mm"
include "fvmpt.mm"
include "adantl.mm"
include "ffvelrnda.mm"
include "nnre.mm"
include "eqeltrd.mm"
include "syldan.mm"
include "sylan2.mm"
include "c1.mm"
include "caddc.mm"
include "peano2nn.mm"
include "ffvelrn.mm"
include "syl2an.mm"
include "peano2rem.mm"
include "syl.mm"
include "simpll.mm"
include "wb.mm"
include "zltlem1.mm"
include "syl2anc.mm"
include "mpbid.mm"
include "lesub1dd.mm"
include "recnd.mm"
include "1cnd.mm"
include "sub32d.mm"
include "subsub4d.mm"
include "eqtrd.mm"
include "breqtrd.mm"
include "3brtr4d.mm"
include "monoord.mm"
include "3brtr3d.mm"
include "ltletrd.mm"
include "ltsub1d.mm"
include "mpbird.mm"
include "ex.mm"
include "ralrimivva.mm"
include "ssralv.mm"
include "ralimdv.mm"
include "syld.mm"
include "mpan9.mm"
include "wor.mm"
include "nnssre.mm"
include "ltso.mm"
include "soss.mm"
include "mp2.mm"
include "a1i.mm"
include "adantr.mm"
include "soisores.mm"
include "syl22anc.mm"

theorem isercolllem1
  let wph: wff ph
  let cS: class S
  let vk: setvar k
  let cG: class G
  let cM: class M
  let cZ: class Z
  let vj: setvar j
  let vm: setvar m
  let vn: setvar n
  let vx: setvar x
  let cA: class A
  let cF: class F
  let vy: setvar y
  let cN: class N
  let cH: class H
  assume isercoll.z: |- Z = ( ZZ>= ` M )
  assume isercoll.m: |- ( ph -> M e. ZZ )
  assume isercoll.g: |- ( ph -> G : NN --> Z )
  assume isercoll.i: |- ( ( ph /\ k e. NN ) -> ( G ` k ) < ( G ` ( k + 1 ) ) )

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
  disjoint N k
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
  assert |- ( ( ph /\ S C_ NN ) -> ( G |` S ) Isom < , < ( S , ( G " S ) ) )

  proof
    wph
    cS
    cn
    wss
    #
    wa
    #
    cS
    cG
    cS
    cima
    clt
    clt
    cG
    cS
    cres
    wiso
    #
    vx
    cv
    #
    vy
    cv
    #
    clt
    wbr
    #
    @3
    cG
    cfv
    #
    @4
    cG
    cfv
    #
    clt
    wbr
    #
    wi
    #
    vy
    cS
    wral
    #
    vx
    cS
    wral
    #
    wph
    @9
    vy
    cn
    wral
    #
    vx
    cn
    wral
    #
    @0
    @11
    wph
    @9
    vx
    vy
    cn
    cn
    wph
    @3
    cn
    wcel
    #
    @4
    cn
    wcel
    #
    wa
    #
    wa
    #
    @5
    @8
    @17
    @5
    wa
    #
    @8
    @6
    @4
    cmin
    co
    #
    @7
    @4
    cmin
    co
    #
    clt
    wbr
    @18
    @19
    @6
    @3
    cmin
    co
    #
    @20
    @18
    @6
    @4
    @18
    cZ
    cr
    @6
    cZ
    cz
    cr
    cZ
    cM
    cuz
    cfv
    cz
    isercoll.z
    cM
    uzssz
    eqsstri
    #
    zssre
    sstri
    #
    @18
    cn
    cZ
    @3
    cG
    wph
    cn
    cZ
    cG
    wf
    #
    @16
    @5
    isercoll.g
    ad2antrr
    #
    wph
    @14
    @15
    @5
    simplrl
    #
    ffvelrnd
    sseldi
    #
    @18
    @4
    wph
    @14
    @15
    @5
    simplrr
    #
    nnred
    #
    resubcld
    @18
    @6
    @3
    @27
    @18
    @3
    @26
    nnred
    #
    resubcld
    @18
    @7
    @4
    @18
    cZ
    cr
    @7
    @23
    @18
    cn
    cZ
    @4
    cG
    @25
    @28
    ffvelrnd
    sseldi
    #
    @29
    resubcld
    @18
    @3
    @4
    @6
    @30
    @29
    @27
    @17
    @5
    simpr
    #
    ltsub2dd
    @18
    @3
    vn
    cn
    vn
    cv
    #
    cG
    cfv
    #
    @33
    cmin
    co
    #
    cmpt
    #
    cfv
    #
    @4
    @36
    cfv
    #
    @21
    @20
    cle
    @18
    vk
    @36
    @3
    @4
    @18
    @3
    cz
    wcel
    @4
    cz
    wcel
    @3
    @4
    cle
    wbr
    @4
    @3
    cuz
    cfv
    #
    wcel
    @18
    @3
    @26
    nnzd
    @18
    @4
    @28
    nnzd
    @18
    @3
    @4
    @30
    @29
    @32
    ltled
    @3
    @4
    eluz2
    syl3anbrc
    vk
    cv
    #
    @3
    @4
    cfz
    co
    wcel
    @18
    @40
    @39
    wcel
    #
    @40
    @36
    cfv
    #
    cr
    wcel
    #
    @40
    @3
    @4
    elfzuz
    @18
    @41
    @40
    cn
    wcel
    #
    @43
    @18
    @14
    @41
    @44
    @26
    @40
    @3
    eluznn
    sylan
    #
    @18
    @44
    wa
    #
    @42
    @40
    cG
    cfv
    #
    @40
    cmin
    co
    #
    cr
    @44
    @42
    @48
    wceq
    @18
    vn
    @40
    @35
    @48
    cn
    @36
    vn
    vk
    weq
    #
    @34
    @47
    @33
    @40
    cmin
    @33
    @40
    cG
    fveq2
    @49
    id
    oveq12d
    @36
    eqid
    #
    @47
    @40
    cmin
    ovex
    fvmpt
    adantl
    #
    @46
    @47
    @40
    @46
    cZ
    cr
    @47
    @23
    @18
    cn
    cZ
    @40
    cG
    @25
    ffvelrnda
    #
    sseldi
    #
    @44
    @40
    cr
    wcel
    @18
    @40
    nnre
    adantl
    #
    resubcld
    eqeltrd
    syldan
    sylan2
    @40
    @3
    @4
    c1
    cmin
    co
    #
    cfz
    co
    wcel
    @18
    @41
    @42
    @40
    c1
    caddc
    co
    #
    @36
    cfv
    #
    cle
    wbr
    #
    @40
    @3
    @55
    elfzuz
    @18
    @41
    @44
    @58
    @45
    @46
    @48
    @56
    cG
    cfv
    #
    @56
    cmin
    co
    #
    @42
    @57
    cle
    @46
    @48
    @59
    c1
    cmin
    co
    #
    @40
    cmin
    co
    #
    @60
    cle
    @46
    @47
    @61
    @40
    @53
    @46
    @59
    cr
    wcel
    @61
    cr
    wcel
    @46
    cZ
    cr
    @59
    @23
    @18
    @24
    @56
    cn
    wcel
    #
    @59
    cZ
    wcel
    @44
    @25
    @40
    peano2nn
    #
    cn
    cZ
    @56
    cG
    ffvelrn
    syl2an
    #
    sseldi
    #
    @59
    peano2rem
    syl
    @54
    @46
    @47
    @59
    clt
    wbr
    #
    @47
    @61
    cle
    wbr
    #
    @18
    wph
    @44
    @67
    wph
    @16
    @5
    simpll
    isercoll.i
    sylan
    @46
    @47
    cz
    wcel
    @59
    cz
    wcel
    @67
    @68
    wb
    @46
    cZ
    cz
    @47
    @22
    @52
    sseldi
    @46
    cZ
    cz
    @59
    @22
    @65
    sseldi
    @47
    @59
    zltlem1
    syl2anc
    mpbid
    lesub1dd
    @46
    @62
    @59
    @40
    cmin
    co
    c1
    cmin
    co
    @60
    @46
    @59
    c1
    @40
    @46
    @59
    @66
    recnd
    #
    @46
    1cnd
    #
    @46
    @40
    @54
    recnd
    #
    sub32d
    @46
    @59
    @40
    c1
    @69
    @71
    @70
    subsub4d
    eqtrd
    breqtrd
    @51
    @46
    @63
    @57
    @60
    wceq
    @44
    @63
    @18
    @64
    adantl
    vn
    @56
    @35
    @60
    cn
    @36
    @33
    @56
    wceq
    #
    @34
    @59
    @33
    @56
    cmin
    @33
    @56
    cG
    fveq2
    @72
    id
    oveq12d
    @50
    @59
    @56
    cmin
    ovex
    fvmpt
    syl
    3brtr4d
    syldan
    sylan2
    monoord
    @18
    @14
    @37
    @21
    wceq
    @26
    vn
    @3
    @35
    @21
    cn
    @36
    vn
    vx
    weq
    #
    @34
    @6
    @33
    @3
    cmin
    @33
    @3
    cG
    fveq2
    @73
    id
    oveq12d
    @50
    @6
    @3
    cmin
    ovex
    fvmpt
    syl
    @18
    @15
    @38
    @20
    wceq
    @28
    vn
    @4
    @35
    @20
    cn
    @36
    vn
    vy
    weq
    #
    @34
    @7
    @33
    @4
    cmin
    @33
    @4
    cG
    fveq2
    @74
    id
    oveq12d
    @50
    @7
    @4
    cmin
    ovex
    fvmpt
    syl
    3brtr3d
    ltletrd
    @18
    @6
    @7
    @4
    @27
    @31
    @29
    ltsub1d
    mpbird
    ex
    ralrimivva
    @0
    @13
    @10
    vx
    cn
    wral
    @11
    @0
    @12
    @10
    vx
    cn
    @9
    vy
    cS
    cn
    ssralv
    ralimdv
    @10
    vx
    cS
    cn
    ssralv
    syld
    mpan9
    @1
    cn
    clt
    wor
    #
    cZ
    clt
    wor
    #
    @24
    @0
    @2
    @11
    wb
    @75
    @1
    cn
    cr
    wss
    cr
    clt
    wor
    #
    @75
    nnssre
    ltso
    cn
    cr
    clt
    soss
    mp2
    a1i
    @76
    @1
    cZ
    cr
    wss
    @77
    @76
    @23
    ltso
    cZ
    cr
    clt
    soss
    mp2
    a1i
    wph
    @24
    @0
    isercoll.g
    adantr
    wph
    @0
    simpr
    vx
    vy
    cS
    cn
    cZ
    clt
    clt
    cG
    soisores
    syl22anc
    mpbird
end
