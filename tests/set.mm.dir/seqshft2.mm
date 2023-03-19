include "cfz.mm"
include "co.mm"
include "wcel.mm"
include "cseq.mm"
include "cfv.mm"
include "caddc.mm"
include "wceq.mm"
include "cuz.mm"
include "eluzfz2.mm"
include "syl.mm"
include "wi.mm"
include "cv.mm"
include "c1.mm"
include "eleq1.mm"
include "fveq2.mm"
include "oveq1.mm"
include "fveq2d.mm"
include "eqeq12d.mm"
include "imbi12d.mm"
include "imbi2d.mm"
include "cz.mm"
include "ralrimiva.mm"
include "eluzfz1.mm"
include "rspcdva.mm"
include "eluzel2.mm"
include "seq1.mm"
include "zaddcld.mm"
include "3eqtr4d.mm"
include "a1i13.mm"
include "wa.mm"
include "peano2fzr.mm"
include "adantl.mm"
include "expr.mm"
include "imim1d.mm"
include "simprl.mm"
include "seqp1.mm"
include "adantr.mm"
include "eluzadd.mm"
include "syl2anc.mm"
include "eluzelz.mm"
include "cc.mm"
include "zcn.mm"
include "ax-1cn.mm"
include "add32.mm"
include "mp3an2.mm"
include "syl2an.mm"
include "wral.mm"
include "simprr.mm"
include "eqtrd.mm"
include "oveq2d.mm"
include "syl5ibr.mm"
include "a2d.mm"
include "syld.mm"
include "expcom.mm"
include "uzind4.mm"
include "mpcom.mm"
include "mpd.mm"

theorem seqshft2
  let wph: wff ph
  let c.pl: class .+
  let vk: setvar k
  let cF: class F
  let cG: class G
  let cK: class K
  let cM: class M
  let cN: class N
  let vn: setvar n
  let vx: setvar x
  assume seqshft2.1: |- ( ph -> N e. ( ZZ>= ` M ) )
  assume seqshft2.2: |- ( ph -> K e. ZZ )
  assume seqshft2.3: |- ( ( ph /\ k e. ( M ... N ) ) -> ( F ` k ) = ( G ` ( k + K ) ) )

  disjoint F k
  disjoint G k
  disjoint K k
  disjoint M k
  disjoint k ph
  disjoint N k
  disjoint k n
  disjoint k x
  disjoint n x
  disjoint F n
  disjoint F x
  disjoint G n
  disjoint G x
  disjoint K n
  disjoint K x
  disjoint M n
  disjoint M x
  disjoint n ph
  disjoint ph x
  disjoint N n
  disjoint N x
  disjoint .+ n
  disjoint .+ x
  assert |- ( ph -> ( seq M ( .+ , F ) ` N ) = ( seq ( M + K ) ( .+ , G ) ` ( N + K ) ) )

  proof
    wph
    cN
    cM
    cN
    cfz
    co
    #
    wcel
    #
    cN
    c.pl
    cF
    cM
    cseq
    #
    cfv
    #
    cN
    cK
    caddc
    co
    #
    c.pl
    cG
    cM
    cK
    caddc
    co
    #
    cseq
    #
    cfv
    #
    wceq
    #
    wph
    cN
    cM
    cuz
    cfv
    #
    wcel
    #
    @1
    seqshft2.1
    cM
    cN
    eluzfz2
    syl
    @10
    wph
    @1
    @8
    wi
    #
    seqshft2.1
    wph
    vx
    cv
    #
    @0
    wcel
    #
    @12
    @2
    cfv
    #
    @12
    cK
    caddc
    co
    #
    @6
    cfv
    #
    wceq
    #
    wi
    #
    wi
    wph
    cM
    @0
    wcel
    #
    cM
    @2
    cfv
    #
    @5
    @6
    cfv
    #
    wceq
    #
    wi
    #
    wi
    wph
    vn
    cv
    #
    @0
    wcel
    #
    @24
    @2
    cfv
    #
    @24
    cK
    caddc
    co
    #
    @6
    cfv
    #
    wceq
    #
    wi
    #
    wi
    wph
    @24
    c1
    caddc
    co
    #
    @0
    wcel
    #
    @31
    @2
    cfv
    #
    @31
    cK
    caddc
    co
    #
    @6
    cfv
    #
    wceq
    #
    wi
    #
    wi
    wph
    @11
    wi
    vx
    vn
    cM
    cN
    @12
    cM
    wceq
    #
    @18
    @23
    wph
    @38
    @13
    @19
    @17
    @22
    @12
    cM
    @0
    eleq1
    @38
    @14
    @20
    @16
    @21
    @12
    cM
    @2
    fveq2
    @38
    @15
    @5
    @6
    @12
    cM
    cK
    caddc
    oveq1
    fveq2d
    eqeq12d
    imbi12d
    imbi2d
    @12
    @24
    wceq
    #
    @18
    @30
    wph
    @39
    @13
    @25
    @17
    @29
    @12
    @24
    @0
    eleq1
    @39
    @14
    @26
    @16
    @28
    @12
    @24
    @2
    fveq2
    @39
    @15
    @27
    @6
    @12
    @24
    cK
    caddc
    oveq1
    fveq2d
    eqeq12d
    imbi12d
    imbi2d
    @12
    @31
    wceq
    #
    @18
    @37
    wph
    @40
    @13
    @32
    @17
    @36
    @12
    @31
    @0
    eleq1
    @40
    @14
    @33
    @16
    @35
    @12
    @31
    @2
    fveq2
    @40
    @15
    @34
    @6
    @12
    @31
    cK
    caddc
    oveq1
    fveq2d
    eqeq12d
    imbi12d
    imbi2d
    @12
    cN
    wceq
    #
    @18
    @11
    wph
    @41
    @13
    @1
    @17
    @8
    @12
    cN
    @0
    eleq1
    @41
    @14
    @3
    @16
    @7
    @12
    cN
    @2
    fveq2
    @41
    @15
    @4
    @6
    @12
    cN
    cK
    caddc
    oveq1
    fveq2d
    eqeq12d
    imbi12d
    imbi2d
    cM
    cz
    wcel
    #
    wph
    @19
    @22
    wph
    cM
    cF
    cfv
    #
    @5
    cG
    cfv
    #
    @20
    @21
    wph
    vk
    cv
    #
    cF
    cfv
    #
    @45
    cK
    caddc
    co
    #
    cG
    cfv
    #
    wceq
    #
    @43
    @44
    wceq
    vk
    @0
    cM
    @45
    cM
    wceq
    #
    @46
    @43
    @48
    @44
    @45
    cM
    cF
    fveq2
    @50
    @47
    @5
    cG
    @45
    cM
    cK
    caddc
    oveq1
    fveq2d
    eqeq12d
    wph
    @49
    vk
    @0
    seqshft2.3
    ralrimiva
    #
    wph
    @10
    @19
    seqshft2.1
    cM
    cN
    eluzfz1
    syl
    rspcdva
    wph
    @42
    @20
    @43
    wceq
    wph
    @10
    @42
    seqshft2.1
    cM
    cN
    eluzel2
    syl
    #
    c.pl
    cF
    cM
    seq1
    syl
    wph
    @5
    cz
    wcel
    @21
    @44
    wceq
    wph
    cM
    cK
    @52
    seqshft2.2
    zaddcld
    c.pl
    cG
    @5
    seq1
    syl
    3eqtr4d
    a1i13
    @24
    @9
    wcel
    #
    wph
    @30
    @37
    wph
    @53
    @30
    @37
    wi
    wph
    @53
    wa
    #
    @30
    @32
    @29
    wi
    @37
    @54
    @32
    @25
    @29
    wph
    @53
    @32
    @25
    @53
    @32
    wa
    #
    @25
    wph
    @24
    cM
    cN
    peano2fzr
    adantl
    expr
    imim1d
    @54
    @32
    @29
    @36
    wph
    @53
    @32
    @29
    @36
    wi
    @29
    @36
    wph
    @55
    wa
    #
    @26
    @31
    cF
    cfv
    #
    c.pl
    co
    #
    @28
    @57
    c.pl
    co
    #
    wceq
    @26
    @28
    @57
    c.pl
    oveq1
    @56
    @33
    @58
    @35
    @59
    @56
    @53
    @33
    @58
    wceq
    wph
    @53
    @32
    simprl
    #
    c.pl
    cF
    cM
    @24
    seqp1
    syl
    @56
    @27
    c1
    caddc
    co
    #
    @6
    cfv
    #
    @28
    @61
    cG
    cfv
    #
    c.pl
    co
    #
    @35
    @59
    @56
    @27
    @5
    cuz
    cfv
    wcel
    #
    @62
    @64
    wceq
    @56
    @53
    cK
    cz
    wcel
    #
    @65
    @60
    wph
    @66
    @55
    seqshft2.2
    adantr
    #
    cK
    cM
    @24
    eluzadd
    syl2anc
    c.pl
    cG
    @5
    @27
    seqp1
    syl
    @56
    @34
    @61
    @6
    @56
    @24
    cz
    wcel
    #
    @66
    @34
    @61
    wceq
    #
    @56
    @53
    @68
    @60
    cM
    @24
    eluzelz
    syl
    @67
    @68
    @24
    cc
    wcel
    #
    cK
    cc
    wcel
    #
    @69
    @66
    @24
    zcn
    cK
    zcn
    @70
    c1
    cc
    wcel
    @71
    @69
    ax-1cn
    @24
    c1
    cK
    add32
    mp3an2
    syl2an
    syl2anc
    #
    fveq2d
    @56
    @57
    @63
    @28
    c.pl
    @56
    @57
    @34
    cG
    cfv
    #
    @63
    @56
    @49
    @57
    @73
    wceq
    vk
    @0
    @31
    @45
    @31
    wceq
    #
    @46
    @57
    @48
    @73
    @45
    @31
    cF
    fveq2
    @74
    @47
    @34
    cG
    @45
    @31
    cK
    caddc
    oveq1
    fveq2d
    eqeq12d
    wph
    @49
    vk
    @0
    wral
    @55
    @51
    adantr
    wph
    @53
    @32
    simprr
    rspcdva
    @56
    @34
    @61
    cG
    @72
    fveq2d
    eqtrd
    oveq2d
    3eqtr4d
    eqeq12d
    syl5ibr
    expr
    a2d
    syld
    expcom
    a2d
    uzind4
    mpcom
    mpd
end
