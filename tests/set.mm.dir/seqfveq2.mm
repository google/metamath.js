include "cfz.mm"
include "co.mm"
include "wcel.mm"
include "cseq.mm"
include "cfv.mm"
include "wceq.mm"
include "cuz.mm"
include "eluzfz2.mm"
include "syl.mm"
include "wi.mm"
include "cv.mm"
include "c1.mm"
include "caddc.mm"
include "eleq1.mm"
include "fveq2.mm"
include "eqeq12d.mm"
include "imbi12d.mm"
include "imbi2d.mm"
include "cz.mm"
include "eluzelz.mm"
include "seq1.mm"
include "eqtr4d.mm"
include "a1d.mm"
include "a1i.mm"
include "wa.mm"
include "peano2fzr.mm"
include "adantl.mm"
include "expr.mm"
include "imim1d.mm"
include "oveq1.mm"
include "simpl.mm"
include "uztrn.mm"
include "syl2anr.mm"
include "seqp1.mm"
include "ad2antrl.mm"
include "wral.mm"
include "eluzp1p1.mm"
include "elfzuz3.mm"
include "ad2antll.mm"
include "elfzuzb.mm"
include "sylanbrc.mm"
include "ralrimiva.mm"
include "adantr.mm"
include "rspcv.mm"
include "sylc.mm"
include "oveq2d.mm"
include "syl5ibr.mm"
include "a2d.mm"
include "syld.mm"
include "expcom.mm"
include "uzind4.mm"
include "mpcom.mm"
include "mpd.mm"

theorem seqfveq2
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
  assume seqfveq2.1: |- ( ph -> K e. ( ZZ>= ` M ) )
  assume seqfveq2.2: |- ( ph -> ( seq M ( .+ , F ) ` K ) = ( G ` K ) )
  assume seqfveq2.3: |- ( ph -> N e. ( ZZ>= ` K ) )
  assume seqfveq2.4: |- ( ( ph /\ k e. ( ( K + 1 ) ... N ) ) -> ( F ` k ) = ( G ` k ) )

  disjoint F k
  disjoint G k
  disjoint K k
  disjoint N k
  disjoint k ph
  disjoint k n
  disjoint k x
  disjoint n x
  disjoint F n
  disjoint F x
  disjoint G n
  disjoint G x
  disjoint K n
  disjoint K x
  disjoint N n
  disjoint N x
  disjoint n ph
  disjoint ph x
  disjoint M n
  disjoint M x
  disjoint .+ n
  disjoint .+ x
  assert |- ( ph -> ( seq M ( .+ , F ) ` N ) = ( seq K ( .+ , G ) ` N ) )

  proof
    wph
    cN
    cK
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
    c.pl
    cG
    cK
    cseq
    #
    cfv
    #
    wceq
    #
    wph
    cN
    cK
    cuz
    cfv
    #
    wcel
    #
    @1
    seqfveq2.3
    cK
    cN
    eluzfz2
    syl
    @8
    wph
    @1
    @6
    wi
    #
    seqfveq2.3
    wph
    vx
    cv
    #
    @0
    wcel
    #
    @10
    @2
    cfv
    #
    @10
    @4
    cfv
    #
    wceq
    #
    wi
    #
    wi
    wph
    cK
    @0
    wcel
    #
    cK
    @2
    cfv
    #
    cK
    @4
    cfv
    #
    wceq
    #
    wi
    #
    wi
    #
    wph
    vn
    cv
    #
    @0
    wcel
    #
    @22
    @2
    cfv
    #
    @22
    @4
    cfv
    #
    wceq
    #
    wi
    #
    wi
    wph
    @22
    c1
    caddc
    co
    #
    @0
    wcel
    #
    @28
    @2
    cfv
    #
    @28
    @4
    cfv
    #
    wceq
    #
    wi
    #
    wi
    wph
    @9
    wi
    vx
    vn
    cK
    cN
    @10
    cK
    wceq
    #
    @15
    @20
    wph
    @34
    @11
    @16
    @14
    @19
    @10
    cK
    @0
    eleq1
    @34
    @12
    @17
    @13
    @18
    @10
    cK
    @2
    fveq2
    @10
    cK
    @4
    fveq2
    eqeq12d
    imbi12d
    imbi2d
    @10
    @22
    wceq
    #
    @15
    @27
    wph
    @35
    @11
    @23
    @14
    @26
    @10
    @22
    @0
    eleq1
    @35
    @12
    @24
    @13
    @25
    @10
    @22
    @2
    fveq2
    @10
    @22
    @4
    fveq2
    eqeq12d
    imbi12d
    imbi2d
    @10
    @28
    wceq
    #
    @15
    @33
    wph
    @36
    @11
    @29
    @14
    @32
    @10
    @28
    @0
    eleq1
    @36
    @12
    @30
    @13
    @31
    @10
    @28
    @2
    fveq2
    @10
    @28
    @4
    fveq2
    eqeq12d
    imbi12d
    imbi2d
    @10
    cN
    wceq
    #
    @15
    @9
    wph
    @37
    @11
    @1
    @14
    @6
    @10
    cN
    @0
    eleq1
    @37
    @12
    @3
    @13
    @5
    @10
    cN
    @2
    fveq2
    @10
    cN
    @4
    fveq2
    eqeq12d
    imbi12d
    imbi2d
    @21
    cK
    cz
    wcel
    #
    wph
    @19
    @16
    wph
    @17
    cK
    cG
    cfv
    #
    @18
    seqfveq2.2
    wph
    @38
    @18
    @39
    wceq
    wph
    cK
    cM
    cuz
    cfv
    #
    wcel
    #
    @38
    seqfveq2.1
    cM
    cK
    eluzelz
    syl
    c.pl
    cG
    cK
    seq1
    syl
    eqtr4d
    a1d
    a1i
    @22
    @7
    wcel
    #
    wph
    @27
    @33
    wph
    @42
    @27
    @33
    wi
    wph
    @42
    wa
    #
    @27
    @29
    @26
    wi
    @33
    @43
    @29
    @23
    @26
    wph
    @42
    @29
    @23
    @42
    @29
    wa
    #
    @23
    wph
    @22
    cK
    cN
    peano2fzr
    adantl
    expr
    imim1d
    @43
    @29
    @26
    @32
    wph
    @42
    @29
    @26
    @32
    wi
    @26
    @32
    wph
    @44
    wa
    #
    @24
    @28
    cF
    cfv
    #
    c.pl
    co
    #
    @25
    @46
    c.pl
    co
    #
    wceq
    @24
    @25
    @46
    c.pl
    oveq1
    @45
    @30
    @47
    @31
    @48
    @45
    @22
    @40
    wcel
    #
    @30
    @47
    wceq
    @44
    @42
    @41
    @49
    wph
    @42
    @29
    simpl
    seqfveq2.1
    cK
    @22
    cM
    uztrn
    syl2anr
    c.pl
    cF
    cM
    @22
    seqp1
    syl
    @45
    @31
    @25
    @28
    cG
    cfv
    #
    c.pl
    co
    #
    @48
    @42
    @31
    @51
    wceq
    wph
    @29
    c.pl
    cG
    cK
    @22
    seqp1
    ad2antrl
    @45
    @46
    @50
    @25
    c.pl
    @45
    @28
    cK
    c1
    caddc
    co
    #
    cN
    cfz
    co
    #
    wcel
    #
    vk
    cv
    #
    cF
    cfv
    #
    @55
    cG
    cfv
    #
    wceq
    #
    vk
    @53
    wral
    #
    @46
    @50
    wceq
    #
    @45
    @28
    @52
    cuz
    cfv
    wcel
    #
    cN
    @28
    cuz
    cfv
    wcel
    #
    @54
    @42
    @61
    wph
    @29
    cK
    @22
    eluzp1p1
    ad2antrl
    @29
    @62
    wph
    @42
    @28
    cK
    cN
    elfzuz3
    ad2antll
    @28
    @52
    cN
    elfzuzb
    sylanbrc
    wph
    @59
    @44
    wph
    @58
    vk
    @53
    seqfveq2.4
    ralrimiva
    adantr
    @58
    @60
    vk
    @28
    @53
    @55
    @28
    wceq
    @56
    @46
    @57
    @50
    @55
    @28
    cF
    fveq2
    @55
    @28
    cG
    fveq2
    eqeq12d
    rspcv
    sylc
    oveq2d
    eqtr4d
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
