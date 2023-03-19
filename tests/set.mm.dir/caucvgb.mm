include "cz.mm"
include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "cfv.mm"
include "cc.mm"
include "cuz.mm"
include "wral.mm"
include "wrex.mm"
include "cli.mm"
include "cdm.mm"
include "cmin.mm"
include "co.mm"
include "cabs.mm"
include "clt.mm"
include "wbr.mm"
include "crp.mm"
include "cop.mm"
include "wex.mm"
include "eldm2g.mm"
include "ibi.mm"
include "df-br.mm"
include "c1.mm"
include "simpll.mm"
include "1rp.mm"
include "a1i.mm"
include "eqidd.mm"
include "simpr.mm"
include "climi.mm"
include "simpl.mm"
include "ralimi.mm"
include "reximi.mm"
include "syl.mm"
include "ex.mm"
include "syl5bir.mm"
include "exlimdv.mm"
include "syl5.mm"
include "wi.mm"
include "wb.mm"
include "wceq.mm"
include "weq.mm"
include "fveq2.mm"
include "raleqdv.mm"
include "cbvrexv.mm"
include "rspcv.mm"
include "mpsyl.mm"
include "eluzelz.mm"
include "eleq2s.mm"
include "eqid.mm"
include "climcau.mm"
include "sylan.mm"
include "r19.29uz.mm"
include "ralimdv.mm"
include "mpan9.mm"
include "an32s.mm"
include "adantll.mm"
include "simplrr.mm"
include "eleq1d.mm"
include "rspccva.mm"
include "oveq1d.mm"
include "fveq2d.mm"
include "breq1d.mm"
include "cbvralv.mm"
include "sylib.mm"
include "adantl.mm"
include "oveq2d.mm"
include "raleqbidv.mm"
include "breq2.mm"
include "rexralbidv.mm"
include "syl5bb.mm"
include "caucvg.mm"
include "adantlll.mm"
include "impbida.mm"
include "cau4.mm"
include "ad2antrl.mm"
include "bitr4d.mm"
include "rexlimdvaa.mm"
include "pm5.21ndd.mm"

theorem caucvgb
  let vx: setvar x
  let vj: setvar j
  let vk: setvar k
  let cF: class F
  let cM: class M
  let cV: class V
  let cZ: class Z
  let vi: setvar i
  let vm: setvar m
  let vn: setvar n
  let vy: setvar y
  let wph: wff ph
  assume caucvgb.1: |- Z = ( ZZ>= ` M )

  disjoint j k
  disjoint j x
  disjoint F j
  disjoint k x
  disjoint F k
  disjoint F x
  disjoint M j
  disjoint M k
  disjoint M x
  disjoint Z j
  disjoint Z k
  disjoint Z x
  disjoint V k
  disjoint i j
  disjoint i k
  disjoint i m
  disjoint i n
  disjoint i x
  disjoint i y
  disjoint F i
  disjoint j m
  disjoint j n
  disjoint j y
  disjoint k m
  disjoint k n
  disjoint k y
  disjoint m n
  disjoint m x
  disjoint m y
  disjoint F m
  disjoint n x
  disjoint n y
  disjoint F n
  disjoint x y
  disjoint F y
  disjoint M m
  disjoint M n
  disjoint Z i
  disjoint Z m
  disjoint Z n
  disjoint Z y
  disjoint j ph
  disjoint k ph
  disjoint n ph
  disjoint ph x
  disjoint V i
  disjoint V m
  disjoint V n
  disjoint V y
  assert |- ( ( M e. ZZ /\ F e. V ) -> ( F e. dom ~~> <-> A. x e. RR+ E. j e. Z A. k e. ( ZZ>= ` j ) ( ( F ` k ) e. CC /\ ( abs ` ( ( F ` k ) - ( F ` j ) ) ) < x ) ) )

  proof
    cM
    cz
    wcel
    #
    cF
    cV
    wcel
    #
    wa
    #
    vk
    cv
    #
    cF
    cfv
    #
    cc
    wcel
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
    cF
    cli
    cdm
    #
    wcel
    #
    @5
    @4
    vj
    cv
    #
    cF
    cfv
    #
    cmin
    co
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
    wa
    #
    vk
    @12
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
    cF
    vm
    cv
    #
    cop
    cli
    wcel
    #
    vm
    wex
    #
    @2
    @9
    @11
    @25
    vm
    cF
    cli
    @10
    eldm2g
    ibi
    @2
    @24
    @9
    vm
    @24
    cF
    @23
    cli
    wbr
    #
    @2
    @9
    cF
    @23
    cli
    df-br
    @2
    @26
    @9
    @2
    @26
    wa
    #
    @5
    @4
    @23
    cmin
    co
    cabs
    cfv
    c1
    clt
    wbr
    #
    wa
    #
    vk
    @7
    wral
    #
    vn
    cZ
    wrex
    @9
    @27
    @23
    @4
    c1
    vn
    vk
    cF
    cM
    cZ
    caucvgb.1
    @0
    @1
    @26
    simpll
    c1
    crp
    wcel
    #
    @27
    1rp
    a1i
    @27
    @3
    cZ
    wcel
    wa
    @4
    eqidd
    @2
    @26
    simpr
    climi
    @30
    @8
    vn
    cZ
    @29
    @5
    vk
    @7
    @5
    @28
    simpl
    ralimi
    reximi
    syl
    ex
    syl5bir
    exlimdv
    syl5
    @22
    @9
    wi
    @2
    @31
    @22
    @5
    vk
    @19
    wral
    #
    vj
    cZ
    wrex
    #
    vx
    crp
    wral
    @9
    1rp
    @21
    @33
    vx
    crp
    @20
    @32
    vj
    cZ
    @18
    @5
    vk
    @19
    @5
    @17
    simpl
    ralimi
    reximi
    ralimi
    @33
    @9
    vx
    c1
    crp
    @33
    @9
    wb
    @16
    c1
    wceq
    @32
    @8
    vj
    vn
    cZ
    vj
    vn
    weq
    @5
    vk
    @19
    @7
    @12
    @6
    cuz
    fveq2
    raleqdv
    cbvrexv
    a1i
    rspcv
    mpsyl
    a1i
    @2
    @8
    @11
    @22
    wb
    vn
    cZ
    @2
    @6
    cZ
    wcel
    #
    @8
    wa
    #
    wa
    #
    @11
    @20
    vj
    @7
    wrex
    #
    vx
    crp
    wral
    #
    @22
    @36
    @11
    @38
    @35
    @11
    @38
    @2
    @34
    @11
    @8
    @38
    @34
    @11
    wa
    @17
    vk
    @19
    wral
    #
    vj
    @7
    wrex
    #
    vx
    crp
    wral
    #
    @8
    @38
    @34
    @6
    cz
    wcel
    #
    @11
    @41
    @42
    @6
    cM
    cuz
    cfv
    cZ
    cM
    @6
    eluzelz
    caucvgb.1
    eleq2s
    vx
    vj
    vk
    cF
    @6
    @7
    @7
    eqid
    #
    climcau
    sylan
    @8
    @40
    @37
    vx
    crp
    @8
    @40
    @37
    @5
    @17
    vj
    vk
    @6
    @7
    @43
    r19.29uz
    ex
    ralimdv
    mpan9
    an32s
    adantll
    @1
    @35
    @38
    @11
    @0
    @1
    @35
    wa
    #
    @38
    wa
    #
    vy
    vi
    vm
    cF
    @6
    cV
    @7
    @43
    @45
    @8
    @23
    @7
    wcel
    @23
    cF
    cfv
    #
    cc
    wcel
    #
    @1
    @34
    @8
    @38
    simplrr
    @5
    @47
    vk
    @23
    @7
    vk
    vm
    weq
    #
    @4
    @46
    cc
    @3
    @23
    cF
    fveq2
    #
    eleq1d
    rspccva
    sylan
    @45
    @46
    @13
    cmin
    co
    #
    cabs
    cfv
    #
    @16
    clt
    wbr
    #
    vm
    @19
    wral
    #
    vj
    @7
    wrex
    #
    vx
    crp
    wral
    #
    @46
    vi
    cv
    #
    cF
    cfv
    #
    cmin
    co
    #
    cabs
    cfv
    #
    vy
    cv
    #
    clt
    wbr
    #
    vm
    @56
    cuz
    cfv
    #
    wral
    vi
    @7
    wrex
    #
    vy
    crp
    wral
    @38
    @55
    @44
    @37
    @54
    vx
    crp
    @20
    @53
    vj
    @7
    @20
    @39
    @53
    @18
    @17
    vk
    @19
    @5
    @17
    simpr
    ralimi
    @17
    @52
    vk
    vm
    @19
    @48
    @15
    @51
    @16
    clt
    @48
    @14
    @50
    cabs
    @48
    @4
    @46
    @13
    cmin
    @49
    oveq1d
    fveq2d
    breq1d
    cbvralv
    sylib
    reximi
    ralimi
    adantl
    @54
    @63
    vx
    vy
    crp
    @54
    @59
    @16
    clt
    wbr
    #
    vm
    @62
    wral
    #
    vi
    @7
    wrex
    vx
    vy
    weq
    #
    @63
    @53
    @65
    vj
    vi
    @7
    vj
    vi
    weq
    #
    @52
    @64
    vm
    @19
    @62
    @12
    @56
    cuz
    fveq2
    @67
    @51
    @59
    @16
    clt
    @67
    @50
    @58
    cabs
    @67
    @13
    @57
    @46
    cmin
    @12
    @56
    cF
    fveq2
    oveq2d
    fveq2d
    breq1d
    raleqbidv
    cbvrexv
    @66
    @64
    @61
    vi
    vm
    @7
    @62
    @16
    @60
    @59
    clt
    breq2
    rexralbidv
    syl5bb
    cbvralv
    sylib
    @1
    @35
    @38
    simpll
    caucvg
    adantlll
    impbida
    @34
    @22
    @38
    wb
    @2
    @8
    vx
    vj
    vk
    cF
    cM
    @6
    @7
    cZ
    caucvgb.1
    @43
    cau4
    ad2antrl
    bitr4d
    rexlimdvaa
    pm5.21ndd
end
