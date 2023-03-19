include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cfz.mm"
include "wcel.mm"
include "cseq.mm"
include "cfv.mm"
include "wceq.mm"
include "cuz.mm"
include "eluzfz2.mm"
include "syl.mm"
include "wi.mm"
include "cv.mm"
include "eleq1.mm"
include "fveq2.mm"
include "oveq2d.mm"
include "eqeq12d.mm"
include "imbi12d.mm"
include "imbi2d.mm"
include "cz.mm"
include "seqp1.mm"
include "eluzel2.mm"
include "seq1.mm"
include "3syl.mm"
include "eqtr4d.mm"
include "a1i13.mm"
include "wa.mm"
include "peano2fzr.mm"
include "adantl.mm"
include "expr.mm"
include "imim1d.mm"
include "oveq1.mm"
include "simprl.mm"
include "peano2uz.mm"
include "adantr.mm"
include "uztrn.mm"
include "syl2anc.mm"
include "simpl.mm"
include "wss.mm"
include "eluzelz.mm"
include "peano2uzr.mm"
include "fzss2.mm"
include "sselda.mm"
include "syldan.mm"
include "seqcl.mm"
include "elfzuz3.mm"
include "fzss1.mm"
include "sstrd.mm"
include "adantlr.mm"
include "eleq1d.mm"
include "wral.mm"
include "ralrimiva.mm"
include "simpr.mm"
include "ssel2.mm"
include "syl2an.mm"
include "rspcdva.mm"
include "caovassg.mm"
include "syl13anc.mm"
include "syl5ibr.mm"
include "a2d.mm"
include "syld.mm"
include "expcom.mm"
include "uzind4.mm"
include "mpcom.mm"
include "mpd.mm"

theorem seqsplit
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let c.pl: class .+
  let cS: class S
  let cF: class F
  let cK: class K
  let cM: class M
  let cN: class N
  let vn: setvar n
  assume seqsplit.1: |- ( ( ph /\ ( x e. S /\ y e. S ) ) -> ( x .+ y ) e. S )
  assume seqsplit.2: |- ( ( ph /\ ( x e. S /\ y e. S /\ z e. S ) ) -> ( ( x .+ y ) .+ z ) = ( x .+ ( y .+ z ) ) )
  assume seqsplit.3: |- ( ph -> N e. ( ZZ>= ` ( M + 1 ) ) )
  assume seqsplit.4: |- ( ph -> M e. ( ZZ>= ` K ) )
  assume seqsplit.5: |- ( ( ph /\ x e. ( K ... N ) ) -> ( F ` x ) e. S )

  disjoint x y
  disjoint x z
  disjoint F x
  disjoint y z
  disjoint F y
  disjoint F z
  disjoint K x
  disjoint K y
  disjoint K z
  disjoint M x
  disjoint M y
  disjoint M z
  disjoint ph x
  disjoint ph y
  disjoint ph z
  disjoint N x
  disjoint N y
  disjoint N z
  disjoint .+ x
  disjoint .+ y
  disjoint .+ z
  disjoint S x
  disjoint S y
  disjoint S z
  disjoint n x
  disjoint n y
  disjoint n z
  disjoint F n
  disjoint K n
  disjoint M n
  disjoint n ph
  disjoint N n
  disjoint .+ n
  assert |- ( ph -> ( seq K ( .+ , F ) ` N ) = ( ( seq K ( .+ , F ) ` M ) .+ ( seq ( M + 1 ) ( .+ , F ) ` N ) ) )

  proof
    wph
    cN
    cM
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
    cN
    c.pl
    cF
    cK
    cseq
    #
    cfv
    #
    cM
    @3
    cfv
    #
    cN
    c.pl
    cF
    @0
    cseq
    #
    cfv
    #
    c.pl
    co
    #
    wceq
    #
    wph
    cN
    @0
    cuz
    cfv
    #
    wcel
    #
    @2
    seqsplit.3
    @0
    cN
    eluzfz2
    syl
    @11
    wph
    @2
    @9
    wi
    #
    seqsplit.3
    wph
    vx
    cv
    #
    @1
    wcel
    #
    @13
    @3
    cfv
    #
    @5
    @13
    @6
    cfv
    #
    c.pl
    co
    #
    wceq
    #
    wi
    #
    wi
    wph
    @0
    @1
    wcel
    #
    @0
    @3
    cfv
    #
    @5
    @0
    @6
    cfv
    #
    c.pl
    co
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
    @1
    wcel
    #
    @26
    @3
    cfv
    #
    @5
    @26
    @6
    cfv
    #
    c.pl
    co
    #
    wceq
    #
    wi
    #
    wi
    wph
    @26
    c1
    caddc
    co
    #
    @1
    wcel
    #
    @33
    @3
    cfv
    #
    @5
    @33
    @6
    cfv
    #
    c.pl
    co
    #
    wceq
    #
    wi
    #
    wi
    wph
    @12
    wi
    vx
    vn
    @0
    cN
    @13
    @0
    wceq
    #
    @19
    @25
    wph
    @40
    @14
    @20
    @18
    @24
    @13
    @0
    @1
    eleq1
    @40
    @15
    @21
    @17
    @23
    @13
    @0
    @3
    fveq2
    @40
    @16
    @22
    @5
    c.pl
    @13
    @0
    @6
    fveq2
    oveq2d
    eqeq12d
    imbi12d
    imbi2d
    @13
    @26
    wceq
    #
    @19
    @32
    wph
    @41
    @14
    @27
    @18
    @31
    @13
    @26
    @1
    eleq1
    @41
    @15
    @28
    @17
    @30
    @13
    @26
    @3
    fveq2
    @41
    @16
    @29
    @5
    c.pl
    @13
    @26
    @6
    fveq2
    oveq2d
    eqeq12d
    imbi12d
    imbi2d
    @13
    @33
    wceq
    #
    @19
    @39
    wph
    @42
    @14
    @34
    @18
    @38
    @13
    @33
    @1
    eleq1
    @42
    @15
    @35
    @17
    @37
    @13
    @33
    @3
    fveq2
    @42
    @16
    @36
    @5
    c.pl
    @13
    @33
    @6
    fveq2
    oveq2d
    eqeq12d
    imbi12d
    imbi2d
    @13
    cN
    wceq
    #
    @19
    @12
    wph
    @43
    @14
    @2
    @18
    @9
    @13
    cN
    @1
    eleq1
    @43
    @15
    @4
    @17
    @8
    @13
    cN
    @3
    fveq2
    @43
    @16
    @7
    @5
    c.pl
    @13
    cN
    @6
    fveq2
    oveq2d
    eqeq12d
    imbi12d
    imbi2d
    @0
    cz
    wcel
    #
    wph
    @20
    @24
    wph
    @21
    @5
    @0
    cF
    cfv
    #
    c.pl
    co
    #
    @23
    wph
    cM
    cK
    cuz
    cfv
    #
    wcel
    #
    @21
    @46
    wceq
    seqsplit.4
    c.pl
    cF
    cK
    cM
    seqp1
    syl
    wph
    @22
    @45
    @5
    c.pl
    wph
    @11
    @44
    @22
    @45
    wceq
    seqsplit.3
    @0
    cN
    eluzel2
    c.pl
    cF
    @0
    seq1
    3syl
    oveq2d
    eqtr4d
    a1i13
    @26
    @10
    wcel
    #
    wph
    @32
    @39
    wph
    @49
    @32
    @39
    wi
    wph
    @49
    wa
    #
    @32
    @34
    @31
    wi
    @39
    @50
    @34
    @27
    @31
    wph
    @49
    @34
    @27
    @49
    @34
    wa
    #
    @27
    wph
    @26
    @0
    cN
    peano2fzr
    adantl
    #
    expr
    imim1d
    @50
    @34
    @31
    @38
    wph
    @49
    @34
    @31
    @38
    wi
    @31
    @38
    wph
    @51
    wa
    #
    @28
    @33
    cF
    cfv
    #
    c.pl
    co
    #
    @30
    @54
    c.pl
    co
    #
    wceq
    @28
    @30
    @54
    c.pl
    oveq1
    @53
    @35
    @55
    @37
    @56
    @53
    @26
    @47
    wcel
    #
    @35
    @55
    wceq
    @53
    @49
    @0
    @47
    wcel
    #
    @57
    wph
    @49
    @34
    simprl
    #
    wph
    @58
    @51
    wph
    @48
    @58
    seqsplit.4
    cK
    cM
    peano2uz
    #
    syl
    adantr
    @0
    @26
    cK
    uztrn
    syl2anc
    c.pl
    cF
    cK
    @26
    seqp1
    syl
    @53
    @37
    @5
    @29
    @54
    c.pl
    co
    #
    c.pl
    co
    #
    @56
    @53
    @36
    @61
    @5
    c.pl
    @53
    @49
    @36
    @61
    wceq
    @59
    c.pl
    cF
    @0
    @26
    seqp1
    syl
    oveq2d
    @53
    wph
    @5
    cS
    wcel
    #
    @29
    cS
    wcel
    @54
    cS
    wcel
    #
    @56
    @62
    wceq
    wph
    @51
    simpl
    wph
    @63
    @51
    wph
    vx
    vy
    c.pl
    cS
    cF
    cK
    cM
    seqsplit.4
    wph
    @13
    cK
    cM
    cfz
    co
    #
    wcel
    @13
    cK
    cN
    cfz
    co
    #
    wcel
    #
    @13
    cF
    cfv
    #
    cS
    wcel
    #
    wph
    @65
    @66
    @13
    wph
    cN
    cM
    cuz
    cfv
    wcel
    #
    @65
    @66
    wss
    wph
    cM
    cz
    wcel
    #
    @11
    @70
    wph
    @48
    @71
    seqsplit.4
    cK
    cM
    eluzelz
    syl
    seqsplit.3
    cM
    cN
    peano2uzr
    syl2anc
    cM
    cK
    cN
    fzss2
    syl
    sselda
    seqsplit.5
    syldan
    seqsplit.1
    seqcl
    adantr
    @53
    vx
    vy
    c.pl
    cS
    cF
    @0
    @26
    @59
    @53
    @13
    @0
    @26
    cfz
    co
    #
    wcel
    @67
    @69
    @53
    @72
    @66
    @13
    @53
    @72
    @1
    @66
    @53
    @27
    cN
    @26
    cuz
    cfv
    wcel
    @72
    @1
    wss
    @52
    @26
    @0
    cN
    elfzuz3
    @26
    @0
    cN
    fzss2
    3syl
    wph
    @1
    @66
    wss
    #
    @51
    wph
    @48
    @58
    @73
    seqsplit.4
    @60
    @0
    cK
    cN
    fzss1
    3syl
    #
    adantr
    sstrd
    sselda
    wph
    @67
    @69
    @51
    seqsplit.5
    adantlr
    syldan
    wph
    @13
    cS
    wcel
    vy
    cv
    #
    cS
    wcel
    wa
    @13
    @75
    c.pl
    co
    cS
    wcel
    @51
    seqsplit.1
    adantlr
    seqcl
    @53
    @69
    @64
    vx
    @66
    @33
    @42
    @68
    @54
    cS
    @13
    @33
    cF
    fveq2
    eleq1d
    wph
    @69
    vx
    @66
    wral
    @51
    wph
    @69
    vx
    @66
    seqsplit.5
    ralrimiva
    adantr
    wph
    @73
    @34
    @33
    @66
    wcel
    @51
    @74
    @49
    @34
    simpr
    @1
    @66
    @33
    ssel2
    syl2an
    rspcdva
    wph
    vx
    vy
    vz
    @5
    @29
    @54
    cS
    c.pl
    seqsplit.2
    caovassg
    syl13anc
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
