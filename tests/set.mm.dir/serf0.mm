include "cc0.mm"
include "cli.mm"
include "wbr.mm"
include "cv.mm"
include "cfv.mm"
include "cabs.mm"
include "clt.mm"
include "cuz.mm"
include "wral.mm"
include "wrex.mm"
include "crp.mm"
include "caddc.mm"
include "cseq.mm"
include "cc.mm"
include "wcel.mm"
include "cmin.mm"
include "co.mm"
include "wa.mm"
include "cdm.mm"
include "cz.mm"
include "wb.mm"
include "caucvgb.mm"
include "syl2anc.mm"
include "mpbid.mm"
include "cau3.mm"
include "sylib.mm"
include "c1.mm"
include "peano2uzs.mm"
include "adantl.mm"
include "wi.mm"
include "eluzelz.mm"
include "uzid.mm"
include "peano2uz.mm"
include "wceq.mm"
include "fveq2.mm"
include "oveq2d.mm"
include "fveq2d.mm"
include "breq1d.mm"
include "rspcv.mm"
include "4syl.mm"
include "adantld.mm"
include "ralimia.mm"
include "simpr.mm"
include "syl6eleq.mm"
include "syl.mm"
include "eluzp1m1.mm"
include "sylan.mm"
include "oveq1.mm"
include "oveq12d.mm"
include "wf.mm"
include "serf.mm"
include "ad2antrr.mm"
include "uztrn2.mm"
include "syldan.mm"
include "ffvelrnd.mm"
include "abssubd.mm"
include "zcnd.mm"
include "ax-1cn.mm"
include "npcan.mm"
include "sylancl.mm"
include "eluzp1p1.mm"
include "eqid.mm"
include "seqm1.mm"
include "oveq1d.mm"
include "adantlr.mm"
include "pncan2d.mm"
include "eqtr2d.mm"
include "3eqtr4d.mm"
include "sylibd.mm"
include "ralrimdva.mm"
include "syl5.mm"
include "raleqdv.mm"
include "rspcev.mm"
include "syl6an.mm"
include "rexlimdva.mm"
include "ralimdv.mm"
include "mpd.mm"
include "eqidd.mm"
include "clim0c.mm"
include "mpbird.mm"

theorem serf0
  let wph: wff ph
  let vk: setvar k
  let cF: class F
  let cM: class M
  let cV: class V
  let cZ: class Z
  let vi: setvar i
  let vj: setvar j
  let vm: setvar m
  let vn: setvar n
  let vx: setvar x
  let vy: setvar y
  assume caucvgb.1: |- Z = ( ZZ>= ` M )
  assume serf0.2: |- ( ph -> M e. ZZ )
  assume serf0.3: |- ( ph -> F e. V )
  assume serf0.4: |- ( ph -> seq M ( + , F ) e. dom ~~> )
  assume serf0.5: |- ( ( ph /\ k e. Z ) -> ( F ` k ) e. CC )

  disjoint F k
  disjoint M k
  disjoint Z k
  disjoint k ph
  disjoint V k
  disjoint i j
  disjoint i k
  disjoint i m
  disjoint i n
  disjoint i x
  disjoint i y
  disjoint F i
  disjoint j k
  disjoint j m
  disjoint j n
  disjoint j x
  disjoint j y
  disjoint F j
  disjoint k m
  disjoint k n
  disjoint k x
  disjoint k y
  disjoint m n
  disjoint m x
  disjoint m y
  disjoint F m
  disjoint n x
  disjoint n y
  disjoint F n
  disjoint x y
  disjoint F x
  disjoint F y
  disjoint M j
  disjoint M m
  disjoint M n
  disjoint M x
  disjoint Z i
  disjoint Z j
  disjoint Z m
  disjoint Z n
  disjoint Z x
  disjoint Z y
  disjoint j ph
  disjoint n ph
  disjoint ph x
  disjoint V i
  disjoint V m
  disjoint V n
  disjoint V y
  assert |- ( ph -> F ~~> 0 )

  proof
    wph
    cF
    cc0
    cli
    wbr
    vk
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
    clt
    wbr
    #
    vk
    vn
    cv
    #
    cuz
    cfv
    #
    wral
    #
    vn
    cZ
    wrex
    #
    vx
    crp
    wral
    #
    wph
    vm
    cv
    #
    caddc
    cF
    cM
    cseq
    #
    cfv
    #
    cc
    wcel
    #
    @12
    @0
    @11
    cfv
    #
    cmin
    co
    #
    cabs
    cfv
    #
    @3
    clt
    wbr
    #
    vk
    @10
    cuz
    cfv
    #
    wral
    #
    wa
    #
    vm
    vj
    cv
    #
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
    @9
    wph
    @13
    @12
    @21
    @11
    cfv
    cmin
    co
    cabs
    cfv
    @3
    clt
    wbr
    wa
    vm
    @22
    wral
    vj
    cZ
    wrex
    vx
    crp
    wral
    #
    @25
    wph
    @11
    cli
    cdm
    #
    wcel
    #
    @26
    serf0.4
    wph
    cM
    cz
    wcel
    #
    @28
    @28
    @26
    wb
    serf0.2
    serf0.4
    vx
    vj
    vm
    @11
    cM
    @27
    cZ
    caucvgb.1
    caucvgb
    syl2anc
    mpbid
    vx
    vj
    vm
    vk
    @11
    cM
    cZ
    caucvgb.1
    cau3
    sylib
    wph
    @24
    @8
    vx
    crp
    wph
    @23
    @8
    vj
    cZ
    wph
    @21
    cZ
    wcel
    #
    wa
    #
    @21
    c1
    caddc
    co
    #
    cZ
    wcel
    #
    @23
    @4
    vk
    @32
    cuz
    cfv
    #
    wral
    #
    @8
    @30
    @33
    wph
    cM
    @21
    cZ
    caucvgb.1
    peano2uzs
    adantl
    #
    @23
    @12
    @10
    c1
    caddc
    co
    #
    @11
    cfv
    #
    cmin
    co
    #
    cabs
    cfv
    #
    @3
    clt
    wbr
    #
    vm
    @22
    wral
    #
    @31
    @35
    @20
    @41
    vm
    @22
    @10
    @22
    wcel
    #
    @19
    @41
    @13
    @43
    @10
    cz
    wcel
    @10
    @18
    wcel
    @37
    @18
    wcel
    @19
    @41
    wi
    @21
    @10
    eluzelz
    @10
    uzid
    @10
    @10
    peano2uz
    @17
    @41
    vk
    @37
    @18
    @0
    @37
    wceq
    #
    @16
    @40
    @3
    clt
    @44
    @15
    @39
    cabs
    @44
    @14
    @38
    @12
    cmin
    @0
    @37
    @11
    fveq2
    oveq2d
    fveq2d
    breq1d
    rspcv
    4syl
    adantld
    ralimia
    @31
    @42
    @4
    vk
    @34
    @31
    @0
    @34
    wcel
    #
    wa
    #
    @42
    @0
    c1
    cmin
    co
    #
    @11
    cfv
    #
    @47
    c1
    caddc
    co
    #
    @11
    cfv
    #
    cmin
    co
    #
    cabs
    cfv
    #
    @3
    clt
    wbr
    #
    @4
    @46
    @47
    @22
    wcel
    #
    @42
    @53
    wi
    @31
    @21
    cz
    wcel
    #
    @45
    @54
    @31
    @21
    cM
    cuz
    cfv
    #
    wcel
    #
    @55
    @31
    @21
    cZ
    @56
    wph
    @30
    simpr
    #
    caucvgb.1
    syl6eleq
    #
    cM
    @21
    eluzelz
    syl
    @21
    @0
    eluzp1m1
    sylan
    #
    @41
    @53
    vm
    @47
    @22
    @10
    @47
    wceq
    #
    @40
    @52
    @3
    clt
    @61
    @39
    @51
    cabs
    @61
    @12
    @48
    @38
    @50
    cmin
    @10
    @47
    @11
    fveq2
    @61
    @37
    @49
    @11
    @10
    @47
    c1
    caddc
    oveq1
    fveq2d
    oveq12d
    fveq2d
    breq1d
    rspcv
    syl
    @46
    @52
    @2
    @3
    clt
    @46
    @48
    @14
    cmin
    co
    #
    cabs
    cfv
    @14
    @48
    cmin
    co
    #
    cabs
    cfv
    @52
    @2
    @46
    @48
    @14
    @46
    cZ
    cc
    @47
    @11
    wph
    cZ
    cc
    @11
    wf
    @30
    @45
    wph
    vk
    cF
    cM
    cZ
    caucvgb.1
    serf0.2
    serf0.5
    serf
    ad2antrr
    #
    @31
    @45
    @54
    @47
    cZ
    wcel
    #
    @60
    @31
    @30
    @54
    @65
    @58
    cM
    @47
    @21
    cZ
    caucvgb.1
    uztrn2
    sylan
    syldan
    ffvelrnd
    #
    @46
    cZ
    cc
    @0
    @11
    @64
    @31
    @33
    @45
    @0
    cZ
    wcel
    #
    @36
    cM
    @0
    @32
    cZ
    caucvgb.1
    uztrn2
    sylan
    #
    ffvelrnd
    abssubd
    @46
    @51
    @62
    cabs
    @46
    @50
    @14
    @48
    cmin
    @46
    @49
    @0
    @11
    @46
    @0
    cc
    wcel
    c1
    cc
    wcel
    @49
    @0
    wceq
    @46
    @0
    @45
    @0
    cz
    wcel
    @31
    @32
    @0
    eluzelz
    adantl
    zcnd
    ax-1cn
    @0
    c1
    npcan
    sylancl
    fveq2d
    oveq2d
    fveq2d
    @46
    @1
    @63
    cabs
    @46
    @63
    @48
    @1
    caddc
    co
    #
    @48
    cmin
    co
    @1
    @46
    @14
    @69
    @48
    cmin
    @46
    @29
    @0
    cM
    c1
    caddc
    co
    #
    cuz
    cfv
    #
    wcel
    #
    @14
    @69
    wceq
    wph
    @29
    @30
    @45
    serf0.2
    ad2antrr
    @31
    @32
    @71
    wcel
    #
    @45
    @72
    @31
    @57
    @73
    @59
    cM
    @21
    eluzp1p1
    syl
    @70
    @0
    @32
    @71
    @71
    eqid
    uztrn2
    sylan
    caddc
    cF
    cM
    @0
    seqm1
    syl2anc
    oveq1d
    @46
    @48
    @1
    @66
    @31
    @45
    @67
    @1
    cc
    wcel
    #
    @68
    wph
    @67
    @74
    @30
    serf0.5
    adantlr
    syldan
    pncan2d
    eqtr2d
    fveq2d
    3eqtr4d
    breq1d
    sylibd
    ralrimdva
    syl5
    @7
    @35
    vn
    @32
    cZ
    @5
    @32
    wceq
    @4
    vk
    @6
    @34
    @5
    @32
    cuz
    fveq2
    raleqdv
    rspcev
    syl6an
    rexlimdva
    ralimdv
    mpd
    wph
    vx
    @1
    vn
    vk
    cF
    cM
    cV
    cZ
    caucvgb.1
    serf0.2
    serf0.3
    wph
    @67
    wa
    @1
    eqidd
    serf0.5
    clim0c
    mpbird
end
