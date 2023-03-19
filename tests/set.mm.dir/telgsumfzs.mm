include "wcel.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cfz.mm"
include "wral.mm"
include "cv.mm"
include "csb.mm"
include "cmpt.mm"
include "cgsu.mm"
include "wceq.mm"
include "cuz.mm"
include "cfv.mm"
include "wi.mm"
include "wa.mm"
include "oveq1.mm"
include "oveq2d.mm"
include "raleqdv.mm"
include "anbi2d.mm"
include "oveq2.mm"
include "mpteq1d.mm"
include "csbeq1d.mm"
include "eqeq12d.mm"
include "imbi12d.mm"
include "cz.mm"
include "csn.mm"
include "eluzel2.mm"
include "syl.mm"
include "adantr.mm"
include "fzsn.mm"
include "cmnd.mm"
include "cgrp.mm"
include "cabl.mm"
include "ablgrp.mm"
include "grpmnd.mm"
include "uzid.mm"
include "peano2uz.mm"
include "eluzfz1.mm"
include "rspcsbela.mm"
include "sylancom.mm"
include "eluzfz2.mm"
include "grpsubcl.mm"
include "syl3anc.mm"
include "csbeq1.mm"
include "oveq12d.mm"
include "adantl.mm"
include "gsumsnd.mm"
include "eqtrd.mm"
include "a1i.mm"
include "telgsumfzslem.mm"
include "ex.mm"
include "wss.mm"
include "cle.mm"
include "wbr.mm"
include "eluzelz.mm"
include "peano2zd.mm"
include "cr.mm"
include "peano2z.mm"
include "zred.mm"
include "lep1d.mm"
include "eluz2.mm"
include "syl3anbrc.mm"
include "fzss2.mm"
include "ssralv.mm"
include "adantld.mm"
include "a2and.mm"
include "uzind4.mm"
include "expd.mm"
include "mpcom.mm"
include "mpd.mm"

theorem telgsumfzs
  let wph: wff ph
  let cB: class B
  let cC: class C
  let vi: setvar i
  let vk: setvar k
  let cG: class G
  let cM: class M
  let c.mi: class .-
  let cN: class N
  let vy: setvar y
  let vx: setvar x
  assume telgsumfzs.b: |- B = ( Base ` G )
  assume telgsumfzs.g: |- ( ph -> G e. Abel )
  assume telgsumfzs.m: |- .- = ( -g ` G )
  assume telgsumfzs.n: |- ( ph -> N e. ( ZZ>= ` M ) )
  assume telgsumfzs.f: |- ( ph -> A. k e. ( M ... ( N + 1 ) ) C e. B )

  disjoint B i
  disjoint B k
  disjoint i k
  disjoint C i
  disjoint G i
  disjoint M i
  disjoint M k
  disjoint .- i
  disjoint i ph
  disjoint N i
  disjoint N k
  disjoint i y
  disjoint k y
  disjoint B x
  disjoint B y
  disjoint x y
  disjoint C x
  disjoint C y
  disjoint G x
  disjoint G y
  disjoint M x
  disjoint M y
  disjoint N x
  disjoint i x
  disjoint k x
  disjoint .- x
  disjoint .- y
  disjoint ph x
  disjoint ph y
  assert |- ( ph -> ( G gsum ( i e. ( M ... N ) |-> ( [_ i / k ]_ C .- [_ ( i + 1 ) / k ]_ C ) ) ) = ( [_ M / k ]_ C .- [_ ( N + 1 ) / k ]_ C ) )

  proof
    wph
    cC
    cB
    wcel
    #
    vk
    cM
    cN
    c1
    caddc
    co
    #
    cfz
    co
    #
    wral
    #
    cG
    vi
    cM
    cN
    cfz
    co
    #
    vk
    vi
    cv
    #
    cC
    csb
    #
    vk
    @5
    c1
    caddc
    co
    #
    cC
    csb
    #
    c.mi
    co
    #
    cmpt
    #
    cgsu
    co
    #
    vk
    cM
    cC
    csb
    #
    vk
    @1
    cC
    csb
    #
    c.mi
    co
    #
    wceq
    #
    telgsumfzs.f
    cN
    cM
    cuz
    cfv
    #
    wcel
    #
    wph
    @3
    @15
    wi
    telgsumfzs.n
    @17
    wph
    @3
    @15
    wph
    @0
    vk
    cM
    vx
    cv
    #
    c1
    caddc
    co
    #
    cfz
    co
    #
    wral
    #
    wa
    #
    cG
    vi
    cM
    @18
    cfz
    co
    #
    @9
    cmpt
    #
    cgsu
    co
    #
    @12
    vk
    @19
    cC
    csb
    #
    c.mi
    co
    #
    wceq
    #
    wi
    wph
    @0
    vk
    cM
    cM
    c1
    caddc
    co
    #
    cfz
    co
    #
    wral
    #
    wa
    #
    cG
    vi
    cM
    cM
    cfz
    co
    #
    @9
    cmpt
    #
    cgsu
    co
    #
    @12
    vk
    @29
    cC
    csb
    #
    c.mi
    co
    #
    wceq
    #
    wi
    #
    wph
    @0
    vk
    cM
    vy
    cv
    #
    c1
    caddc
    co
    #
    cfz
    co
    #
    wral
    #
    wa
    #
    cG
    vi
    cM
    @40
    cfz
    co
    #
    @9
    cmpt
    #
    cgsu
    co
    #
    @12
    vk
    @41
    cC
    csb
    #
    c.mi
    co
    #
    wceq
    #
    wi
    wph
    @0
    vk
    cM
    @41
    c1
    caddc
    co
    #
    cfz
    co
    #
    wral
    #
    wa
    #
    cG
    vi
    @42
    @9
    cmpt
    #
    cgsu
    co
    #
    @12
    vk
    @51
    cC
    csb
    #
    c.mi
    co
    #
    wceq
    #
    wi
    wph
    @3
    wa
    #
    @15
    wi
    vx
    vy
    cM
    cN
    @18
    cM
    wceq
    #
    @22
    @32
    @28
    @38
    @61
    @21
    @31
    wph
    @61
    @0
    vk
    @20
    @30
    @61
    @19
    @29
    cM
    cfz
    @18
    cM
    c1
    caddc
    oveq1
    #
    oveq2d
    raleqdv
    anbi2d
    @61
    @25
    @35
    @27
    @37
    @61
    @24
    @34
    cG
    cgsu
    @61
    vi
    @23
    @33
    @9
    @18
    cM
    cM
    cfz
    oveq2
    mpteq1d
    oveq2d
    @61
    @26
    @36
    @12
    c.mi
    @61
    vk
    @19
    @29
    cC
    @62
    csbeq1d
    oveq2d
    eqeq12d
    imbi12d
    @18
    @40
    wceq
    #
    @22
    @44
    @28
    @50
    @63
    @21
    @43
    wph
    @63
    @0
    vk
    @20
    @42
    @63
    @19
    @41
    cM
    cfz
    @18
    @40
    c1
    caddc
    oveq1
    #
    oveq2d
    raleqdv
    anbi2d
    @63
    @25
    @47
    @27
    @49
    @63
    @24
    @46
    cG
    cgsu
    @63
    vi
    @23
    @45
    @9
    @18
    @40
    cM
    cfz
    oveq2
    mpteq1d
    oveq2d
    @63
    @26
    @48
    @12
    c.mi
    @63
    vk
    @19
    @41
    cC
    @64
    csbeq1d
    oveq2d
    eqeq12d
    imbi12d
    @18
    @41
    wceq
    #
    @22
    @54
    @28
    @59
    @65
    @21
    @53
    wph
    @65
    @0
    vk
    @20
    @52
    @65
    @19
    @51
    cM
    cfz
    @18
    @41
    c1
    caddc
    oveq1
    #
    oveq2d
    raleqdv
    anbi2d
    @65
    @25
    @56
    @27
    @58
    @65
    @24
    @55
    cG
    cgsu
    @65
    vi
    @23
    @42
    @9
    @18
    @41
    cM
    cfz
    oveq2
    mpteq1d
    oveq2d
    @65
    @26
    @57
    @12
    c.mi
    @65
    vk
    @19
    @51
    cC
    @66
    csbeq1d
    oveq2d
    eqeq12d
    imbi12d
    @18
    cN
    wceq
    #
    @22
    @60
    @28
    @15
    @67
    @21
    @3
    wph
    @67
    @0
    vk
    @20
    @2
    @67
    @19
    @1
    cM
    cfz
    @18
    cN
    c1
    caddc
    oveq1
    #
    oveq2d
    raleqdv
    anbi2d
    @67
    @25
    @11
    @27
    @14
    @67
    @24
    @10
    cG
    cgsu
    @67
    vi
    @23
    @4
    @9
    @18
    cN
    cM
    cfz
    oveq2
    mpteq1d
    oveq2d
    @67
    @26
    @13
    @12
    c.mi
    @67
    vk
    @19
    @1
    cC
    @68
    csbeq1d
    oveq2d
    eqeq12d
    imbi12d
    @39
    cM
    cz
    wcel
    #
    @32
    @35
    cG
    vi
    cM
    csn
    #
    @9
    cmpt
    #
    cgsu
    co
    @37
    @32
    @34
    @71
    cG
    cgsu
    @32
    vi
    @33
    @70
    @9
    @32
    @69
    @33
    @70
    wceq
    wph
    @69
    @31
    wph
    @17
    @69
    telgsumfzs.n
    cM
    cN
    eluzel2
    syl
    adantr
    #
    cM
    fzsn
    syl
    mpteq1d
    oveq2d
    @32
    @9
    cB
    @37
    vi
    cG
    cM
    cz
    telgsumfzs.b
    wph
    cG
    cmnd
    wcel
    #
    @31
    wph
    cG
    cgrp
    wcel
    #
    @73
    wph
    cG
    cabl
    wcel
    @74
    telgsumfzs.g
    cG
    ablgrp
    syl
    #
    cG
    grpmnd
    syl
    adantr
    @72
    @32
    @74
    @12
    cB
    wcel
    #
    @36
    cB
    wcel
    #
    @37
    cB
    wcel
    wph
    @74
    @31
    @75
    adantr
    wph
    @31
    cM
    @30
    wcel
    #
    @76
    @32
    @29
    @16
    wcel
    #
    @78
    @32
    cM
    @16
    wcel
    #
    @79
    @32
    @69
    @80
    @72
    cM
    uzid
    syl
    cM
    cM
    peano2uz
    syl
    #
    cM
    @29
    eluzfz1
    syl
    vk
    cM
    @30
    cC
    cB
    rspcsbela
    sylancom
    wph
    @31
    @29
    @30
    wcel
    #
    @77
    @32
    @79
    @82
    @81
    cM
    @29
    eluzfz2
    syl
    vk
    @29
    @30
    cC
    cB
    rspcsbela
    sylancom
    cB
    cG
    c.mi
    @12
    @36
    telgsumfzs.b
    telgsumfzs.m
    grpsubcl
    syl3anc
    @5
    cM
    wceq
    #
    @9
    @37
    wceq
    @32
    @83
    @6
    @12
    @8
    @36
    c.mi
    vk
    @5
    cM
    cC
    csbeq1
    @83
    vk
    @7
    @29
    cC
    @5
    cM
    c1
    caddc
    oveq1
    csbeq1d
    oveq12d
    adantl
    gsumsnd
    eqtrd
    a1i
    @40
    @16
    wcel
    #
    wph
    @43
    @59
    @50
    @53
    @84
    @54
    @50
    @59
    wi
    wph
    vy
    cB
    cC
    vi
    vk
    cG
    cM
    c.mi
    telgsumfzs.b
    telgsumfzs.g
    telgsumfzs.m
    telgsumfzslem
    ex
    @84
    @53
    @43
    wph
    @84
    @42
    @52
    wss
    #
    @53
    @43
    wi
    @84
    @51
    @41
    cuz
    cfv
    wcel
    #
    @85
    @84
    @41
    cz
    wcel
    @51
    cz
    wcel
    @41
    @51
    cle
    wbr
    @86
    @84
    @40
    cM
    @40
    eluzelz
    #
    peano2zd
    #
    @84
    @41
    @88
    peano2zd
    @84
    @41
    @84
    @40
    cz
    wcel
    #
    @41
    cr
    wcel
    @87
    @89
    @41
    @40
    peano2z
    zred
    syl
    lep1d
    @41
    @51
    eluz2
    syl3anbrc
    @41
    cM
    @51
    fzss2
    syl
    @0
    vk
    @42
    @52
    ssralv
    syl
    adantld
    a2and
    uzind4
    expd
    mpcom
    mpd
end
