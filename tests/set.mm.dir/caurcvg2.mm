include "cv.mm"
include "cfv.mm"
include "cr.mm"
include "wcel.mm"
include "cmin.mm"
include "co.mm"
include "cabs.mm"
include "clt.mm"
include "wbr.mm"
include "wa.mm"
include "cuz.mm"
include "wral.mm"
include "wrex.mm"
include "crp.mm"
include "cli.mm"
include "cdm.mm"
include "c0.mm"
include "wne.mm"
include "c1.mm"
include "1rp.mm"
include "ne0ii.mm"
include "r19.2z.mm"
include "sylancr.mm"
include "simpl.mm"
include "ralimi.mm"
include "cmpt.mm"
include "clsp.mm"
include "eqid.mm"
include "simprr.mm"
include "weq.mm"
include "fveq2.mm"
include "eleq1d.mm"
include "rspccva.mm"
include "sylan.mm"
include "fmptd.mm"
include "cc.mm"
include "oveq2d.mm"
include "fveq2d.mm"
include "breq1d.mm"
include "anbi2d.mm"
include "raleqbidv.mm"
include "cbvrexv.mm"
include "oveq1d.mm"
include "anbi12d.mm"
include "cbvralv.mm"
include "recn.mm"
include "anim1i.mm"
include "sylbi.mm"
include "reximi.mm"
include "syl.mm"
include "adantr.mm"
include "wb.mm"
include "cau4.mm"
include "ad2antrl.mm"
include "mpbid.mm"
include "simpr.mm"
include "wceq.mm"
include "uztrn2.mm"
include "fvex.mm"
include "fvmpt.mm"
include "oveq12d.mm"
include "syl5ibr.mm"
include "ralimdva.mm"
include "reximia.mm"
include "caurcvg.mm"
include "cz.mm"
include "eluzelz.mm"
include "eleq2s.mm"
include "cbvmptv.mm"
include "climmpt.mm"
include "syl2anc.mm"
include "mpbird.mm"
include "climrel.mm"
include "releldmi.mm"
include "expr.mm"
include "syl5.mm"
include "rexlimdva.mm"
include "rexlimdvw.mm"
include "mpd.mm"

theorem caurcvg2
  let wph: wff ph
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
  assume caucvg.1: |- Z = ( ZZ>= ` M )
  assume caurcvg2.2: |- ( ph -> F e. V )
  assume caurcvg2.3: |- ( ph -> A. x e. RR+ E. j e. Z A. k e. ( ZZ>= ` j ) ( ( F ` k ) e. RR /\ ( abs ` ( ( F ` k ) - ( F ` j ) ) ) < x ) )

  disjoint j k
  disjoint j x
  disjoint F j
  disjoint k x
  disjoint F k
  disjoint F x
  disjoint M j
  disjoint M k
  disjoint M x
  disjoint j ph
  disjoint k ph
  disjoint ph x
  disjoint Z j
  disjoint Z k
  disjoint Z x
  disjoint i j
  disjoint i k
  disjoint i m
  disjoint i n
  disjoint i x
  disjoint F i
  disjoint j m
  disjoint j n
  disjoint k m
  disjoint k n
  disjoint m n
  disjoint m x
  disjoint F m
  disjoint n x
  disjoint F n
  disjoint M i
  disjoint M m
  disjoint M n
  disjoint i ph
  disjoint m ph
  disjoint n ph
  disjoint Z i
  disjoint Z m
  disjoint Z n
  assert |- ( ph -> F e. dom ~~> )

  proof
    wph
    vk
    cv
    #
    cF
    cfv
    #
    cr
    wcel
    #
    @1
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
    @3
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
    wrex
    #
    cF
    cli
    cdm
    wcel
    #
    wph
    crp
    c0
    wne
    @12
    vx
    crp
    wral
    #
    @13
    c1
    crp
    1rp
    ne0ii
    caurcvg2.3
    @12
    vx
    crp
    r19.2z
    sylancr
    wph
    @12
    @14
    vx
    crp
    wph
    @11
    @14
    vj
    cZ
    @11
    @2
    vk
    @10
    wral
    #
    wph
    @3
    cZ
    wcel
    #
    wa
    @14
    @9
    @2
    vk
    @10
    @2
    @8
    simpl
    ralimi
    wph
    @17
    @16
    @14
    wph
    @17
    @16
    wa
    #
    wa
    #
    cF
    vn
    @10
    vn
    cv
    #
    cF
    cfv
    #
    cmpt
    #
    clsp
    cfv
    #
    cli
    wbr
    #
    @14
    @19
    @24
    @22
    @23
    cli
    wbr
    #
    @19
    vx
    vi
    vm
    @22
    @3
    @10
    @10
    eqid
    #
    @19
    vn
    @10
    @21
    cr
    @22
    @19
    @16
    @20
    @10
    wcel
    @21
    cr
    wcel
    #
    wph
    @17
    @16
    simprr
    @2
    @27
    vk
    @20
    @10
    vk
    vn
    weq
    @1
    @21
    cr
    @0
    @20
    cF
    fveq2
    eleq1d
    rspccva
    sylan
    @22
    eqid
    #
    fmptd
    @19
    vi
    cv
    #
    cF
    cfv
    #
    cc
    wcel
    #
    @30
    vm
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
    @7
    clt
    wbr
    #
    wa
    #
    vi
    @32
    cuz
    cfv
    #
    wral
    #
    vm
    @10
    wrex
    #
    vx
    crp
    wral
    #
    @29
    @22
    cfv
    #
    @32
    @22
    cfv
    #
    cmin
    co
    #
    cabs
    cfv
    #
    @7
    clt
    wbr
    #
    vi
    @38
    wral
    #
    vm
    @10
    wrex
    #
    vx
    crp
    wral
    @19
    @39
    vm
    cZ
    wrex
    #
    vx
    crp
    wral
    #
    @41
    wph
    @50
    @18
    wph
    @15
    @50
    caurcvg2.3
    @12
    @49
    vx
    crp
    @12
    @2
    @1
    @33
    cmin
    co
    #
    cabs
    cfv
    #
    @7
    clt
    wbr
    #
    wa
    #
    vk
    @38
    wral
    #
    vm
    cZ
    wrex
    @49
    @11
    @55
    vj
    vm
    cZ
    vj
    vm
    weq
    #
    @9
    @54
    vk
    @10
    @38
    @3
    @32
    cuz
    fveq2
    @56
    @8
    @53
    @2
    @56
    @6
    @52
    @7
    clt
    @56
    @5
    @51
    cabs
    @56
    @4
    @33
    @1
    cmin
    @3
    @32
    cF
    fveq2
    oveq2d
    fveq2d
    breq1d
    anbi2d
    raleqbidv
    cbvrexv
    @55
    @39
    vm
    cZ
    @55
    @30
    cr
    wcel
    #
    @36
    wa
    #
    vi
    @38
    wral
    @39
    @54
    @58
    vk
    vi
    @38
    vk
    vi
    weq
    #
    @2
    @57
    @53
    @36
    @59
    @1
    @30
    cr
    @0
    @29
    cF
    fveq2
    #
    eleq1d
    @59
    @52
    @35
    @7
    clt
    @59
    @51
    @34
    cabs
    @59
    @1
    @30
    @33
    cmin
    @60
    oveq1d
    fveq2d
    breq1d
    anbi12d
    cbvralv
    @58
    @37
    vi
    @38
    @57
    @31
    @36
    @30
    recn
    anim1i
    ralimi
    sylbi
    reximi
    sylbi
    ralimi
    syl
    adantr
    @17
    @50
    @41
    wb
    wph
    @16
    vx
    vm
    vi
    cF
    cM
    @3
    @10
    cZ
    caucvg.1
    @26
    cau4
    ad2antrl
    mpbid
    @40
    @48
    vx
    crp
    @39
    @47
    vm
    @10
    @32
    @10
    wcel
    #
    @37
    @46
    vi
    @38
    @37
    @46
    @61
    @29
    @38
    wcel
    #
    wa
    #
    @36
    @31
    @36
    simpr
    @63
    @45
    @35
    @7
    clt
    @63
    @44
    @34
    cabs
    @63
    @42
    @30
    @43
    @33
    cmin
    @63
    @29
    @10
    wcel
    @42
    @30
    wceq
    @3
    @29
    @32
    @10
    @26
    uztrn2
    vn
    @29
    @21
    @30
    @10
    @22
    @20
    @29
    cF
    fveq2
    @28
    @29
    cF
    fvex
    fvmpt
    syl
    @61
    @43
    @33
    wceq
    @62
    vn
    @32
    @21
    @33
    @10
    @22
    @20
    @32
    cF
    fveq2
    @28
    @32
    cF
    fvex
    fvmpt
    adantr
    oveq12d
    fveq2d
    breq1d
    syl5ibr
    ralimdva
    reximia
    ralimi
    syl
    caurcvg
    @19
    @3
    cz
    wcel
    #
    cF
    cV
    wcel
    #
    @24
    @25
    wb
    @17
    @64
    wph
    @16
    @64
    @3
    cM
    cuz
    cfv
    cZ
    cM
    @3
    eluzelz
    caucvg.1
    eleq2s
    ad2antrl
    wph
    @65
    @18
    caurcvg2.2
    adantr
    @23
    vk
    cF
    @22
    @3
    cV
    @10
    @26
    vn
    vk
    @10
    @21
    @1
    @20
    @0
    cF
    fveq2
    cbvmptv
    climmpt
    syl2anc
    mpbird
    cF
    @23
    cli
    climrel
    releldmi
    syl
    expr
    syl5
    rexlimdva
    rexlimdvw
    mpd
end
