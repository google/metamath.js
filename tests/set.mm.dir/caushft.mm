include "cca.mm"
include "cfv.mm"
include "wcel.mm"
include "cv.mm"
include "co.mm"
include "clt.mm"
include "wbr.mm"
include "cuz.mm"
include "wral.mm"
include "wrex.mm"
include "crp.mm"
include "cdm.mm"
include "caddc.mm"
include "w3a.mm"
include "cc.mm"
include "cpm.mm"
include "wa.mm"
include "cme.mm"
include "cxmt.mm"
include "metxmet.mm"
include "syl.mm"
include "wceq.mm"
include "ralrimiva.mm"
include "fveq2.mm"
include "oveq1.mm"
include "fveq2d.mm"
include "eqeq12d.mm"
include "rspccva.mm"
include "sylan.mm"
include "iscau4.mm"
include "mpbid.mm"
include "simprd.mm"
include "cz.mm"
include "eleq2i.mm"
include "biimpi.mm"
include "eluzadd.mm"
include "syl2anr.mm"
include "syl6eleqr.mm"
include "cmin.mm"
include "simplr.mm"
include "syl6eleq.mm"
include "eluzelz.mm"
include "ad2antrr.mm"
include "simpr.mm"
include "eluzsub.mm"
include "syl3anc.mm"
include "simp3.mm"
include "ralimi.mm"
include "oveq1d.mm"
include "breq1d.mm"
include "rspcv.mm"
include "syl2im.mm"
include "adantl.mm"
include "zcnd.mm"
include "npcand.mm"
include "wf.mm"
include "uztrn2.mm"
include "ffvelrnd.mm"
include "adantr.mm"
include "metsym.mm"
include "eqtrd.mm"
include "sylibd.mm"
include "ralrimdva.mm"
include "raleqbidv.mm"
include "rspcev.mm"
include "syl6an.mm"
include "rexlimdva.mm"
include "ralimdv.mm"
include "mpd.mm"
include "zaddcld.mm"
include "eqidd.mm"
include "iscauf.mm"
include "mpbird.mm"

theorem caushft
  let wph: wff ph
  let cD: class D
  let vk: setvar k
  let cF: class F
  let cG: class G
  let cM: class M
  let cN: class N
  let cW: class W
  let cX: class X
  let cZ: class Z
  let vj: setvar j
  let vm: setvar m
  let vn: setvar n
  let vx: setvar x
  assume caures.1: |- Z = ( ZZ>= ` M )
  assume caures.3: |- ( ph -> M e. ZZ )
  assume caures.4: |- ( ph -> D e. ( Met ` X ) )
  assume caushft.4: |- W = ( ZZ>= ` ( M + N ) )
  assume caushft.5: |- ( ph -> N e. ZZ )
  assume caushft.7: |- ( ( ph /\ k e. Z ) -> ( F ` k ) = ( G ` ( k + N ) ) )
  assume caushft.8: |- ( ph -> F e. ( Cau ` D ) )
  assume caushft.9: |- ( ph -> G : W --> X )

  disjoint D k
  disjoint G k
  disjoint k ph
  disjoint X k
  disjoint F k
  disjoint N k
  disjoint Z k
  disjoint j k
  disjoint j m
  disjoint j n
  disjoint j x
  disjoint D j
  disjoint k m
  disjoint k n
  disjoint k x
  disjoint m n
  disjoint m x
  disjoint D m
  disjoint n x
  disjoint D n
  disjoint D x
  disjoint G j
  disjoint G m
  disjoint G n
  disjoint G x
  disjoint j ph
  disjoint m ph
  disjoint n ph
  disjoint ph x
  disjoint X j
  disjoint X m
  disjoint X n
  disjoint X x
  disjoint F j
  disjoint F m
  disjoint F x
  disjoint N m
  disjoint N n
  disjoint W j
  disjoint W m
  disjoint W n
  disjoint W x
  disjoint Z j
  disjoint Z m
  disjoint Z x
  disjoint M j
  disjoint M n
  assert |- ( ph -> G e. ( Cau ` D ) )

  proof
    wph
    cG
    cD
    cca
    cfv
    #
    wcel
    vn
    cv
    #
    cG
    cfv
    #
    vm
    cv
    #
    cG
    cfv
    #
    cD
    co
    #
    vx
    cv
    #
    clt
    wbr
    #
    vm
    @1
    cuz
    cfv
    #
    wral
    #
    vn
    cW
    wrex
    #
    vx
    crp
    wral
    #
    wph
    vk
    cv
    #
    cF
    cdm
    wcel
    #
    @12
    cN
    caddc
    co
    #
    cG
    cfv
    #
    cX
    wcel
    #
    @15
    vj
    cv
    #
    cN
    caddc
    co
    #
    cG
    cfv
    #
    cD
    co
    #
    @6
    clt
    wbr
    #
    w3a
    #
    vk
    @17
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
    crp
    wral
    #
    @11
    wph
    cF
    cX
    cc
    cpm
    co
    wcel
    #
    @26
    wph
    cF
    @0
    wcel
    @27
    @26
    wa
    caushft.8
    wph
    vx
    @15
    @19
    cD
    vj
    vk
    cF
    cM
    cX
    cZ
    caures.1
    wph
    cD
    cX
    cme
    cfv
    wcel
    #
    cD
    cX
    cxmt
    cfv
    wcel
    caures.4
    cD
    cX
    metxmet
    syl
    #
    caures.3
    caushft.7
    wph
    @12
    cF
    cfv
    #
    @15
    wceq
    #
    vk
    cZ
    wral
    @17
    cZ
    wcel
    #
    @17
    cF
    cfv
    #
    @19
    wceq
    #
    wph
    @31
    vk
    cZ
    caushft.7
    ralrimiva
    @31
    @34
    vk
    @17
    cZ
    @12
    @17
    wceq
    #
    @30
    @33
    @15
    @19
    @12
    @17
    cF
    fveq2
    @35
    @14
    @18
    cG
    @12
    @17
    cN
    caddc
    oveq1
    fveq2d
    eqeq12d
    rspccva
    sylan
    iscau4
    mpbid
    simprd
    wph
    @25
    @10
    vx
    crp
    wph
    @24
    @10
    vj
    cZ
    wph
    @32
    wa
    #
    @18
    cW
    wcel
    #
    @24
    @19
    @4
    cD
    co
    #
    @6
    clt
    wbr
    #
    vm
    @18
    cuz
    cfv
    #
    wral
    #
    @10
    @36
    @18
    cM
    cN
    caddc
    co
    #
    cuz
    cfv
    #
    cW
    @32
    @17
    cM
    cuz
    cfv
    #
    wcel
    #
    cN
    cz
    wcel
    #
    @18
    @43
    wcel
    wph
    @32
    @45
    cZ
    @44
    @17
    caures.1
    eleq2i
    biimpi
    caushft.5
    cN
    cM
    @17
    eluzadd
    syl2anr
    caushft.4
    syl6eleqr
    #
    @36
    @24
    @39
    vm
    @40
    @36
    @3
    @40
    wcel
    #
    wa
    #
    @24
    @3
    cN
    cmin
    co
    #
    cN
    caddc
    co
    #
    cG
    cfv
    #
    @19
    cD
    co
    #
    @6
    clt
    wbr
    #
    @39
    @49
    @50
    @23
    wcel
    #
    @24
    @21
    vk
    @23
    wral
    @54
    @49
    @17
    cz
    wcel
    #
    @46
    @48
    @55
    @49
    @45
    @56
    @49
    @17
    cZ
    @44
    wph
    @32
    @48
    simplr
    caures.1
    syl6eleq
    cM
    @17
    eluzelz
    syl
    wph
    @46
    @32
    @48
    caushft.5
    ad2antrr
    @36
    @48
    simpr
    cN
    @17
    @3
    eluzsub
    syl3anc
    @22
    @21
    vk
    @23
    @13
    @16
    @21
    simp3
    ralimi
    @21
    @54
    vk
    @50
    @23
    @12
    @50
    wceq
    #
    @20
    @53
    @6
    clt
    @57
    @15
    @52
    @19
    cD
    @57
    @14
    @51
    cG
    @12
    @50
    cN
    caddc
    oveq1
    fveq2d
    oveq1d
    breq1d
    rspcv
    syl2im
    @49
    @53
    @38
    @6
    clt
    @49
    @53
    @4
    @19
    cD
    co
    #
    @38
    @49
    @52
    @4
    @19
    cD
    @49
    @51
    @3
    cG
    @49
    @3
    cN
    @49
    @3
    @48
    @3
    cz
    wcel
    @36
    @18
    @3
    eluzelz
    adantl
    zcnd
    wph
    cN
    cc
    wcel
    @32
    @48
    wph
    cN
    caushft.5
    zcnd
    ad2antrr
    npcand
    fveq2d
    oveq1d
    @49
    @28
    @4
    cX
    wcel
    @19
    cX
    wcel
    #
    @58
    @38
    wceq
    wph
    @28
    @32
    @48
    caures.4
    ad2antrr
    @49
    cW
    cX
    @3
    cG
    wph
    cW
    cX
    cG
    wf
    #
    @32
    @48
    caushft.9
    ad2antrr
    @36
    @37
    @48
    @3
    cW
    wcel
    #
    @47
    @42
    @3
    @18
    cW
    caushft.4
    uztrn2
    sylan
    ffvelrnd
    @36
    @59
    @48
    @36
    cW
    cX
    @18
    cG
    wph
    @60
    @32
    caushft.9
    adantr
    @47
    ffvelrnd
    adantr
    @4
    @19
    cD
    cX
    metsym
    syl3anc
    eqtrd
    breq1d
    sylibd
    ralrimdva
    @9
    @41
    vn
    @18
    cW
    @1
    @18
    wceq
    #
    @7
    @39
    vm
    @8
    @40
    @1
    @18
    cuz
    fveq2
    @62
    @5
    @38
    @6
    clt
    @62
    @2
    @19
    @4
    cD
    @1
    @18
    cG
    fveq2
    oveq1d
    breq1d
    raleqbidv
    rspcev
    syl6an
    rexlimdva
    ralimdv
    mpd
    wph
    vx
    @4
    @2
    cD
    vn
    vm
    cG
    @42
    cX
    cW
    caushft.4
    @29
    wph
    cM
    cN
    caures.3
    caushft.5
    zaddcld
    wph
    @61
    wa
    @4
    eqidd
    wph
    @1
    cW
    wcel
    wa
    @2
    eqidd
    caushft.9
    iscauf
    mpbird
end
