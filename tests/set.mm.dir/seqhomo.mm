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
include "fveq2d.mm"
include "eqeq12d.mm"
include "imbi12d.mm"
include "imbi2d.mm"
include "cz.mm"
include "wral.mm"
include "eluzfz1.mm"
include "ralrimiva.mm"
include "rspcv.mm"
include "sylc.mm"
include "eluzel2.mm"
include "seq1.mm"
include "3syl.mm"
include "3eqtr4d.mm"
include "a1d.mm"
include "a1i.mm"
include "wa.mm"
include "simprl.mm"
include "simprr.mm"
include "peano2fzr.mm"
include "syl2anc.mm"
include "expr.mm"
include "imim1d.mm"
include "oveq1.mm"
include "seqp1.mm"
include "ad2antrl.mm"
include "ralrimivva.mm"
include "adantr.mm"
include "wss.mm"
include "elfzuz3.mm"
include "fzss2.mm"
include "sselda.mm"
include "adantlr.mm"
include "syldan.mm"
include "seqcl.mm"
include "eleq1d.mm"
include "oveq1d.mm"
include "oveq2.mm"
include "oveq2d.mm"
include "rspc2v.mm"
include "mpd.mm"
include "3eqtrd.mm"
include "syl5ibr.mm"
include "a2d.mm"
include "syld.mm"
include "expcom.mm"
include "uzind4.mm"
include "mpcom.mm"

theorem seqhomo
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let c.pl: class .+
  let cQ: class Q
  let cS: class S
  let cF: class F
  let cG: class G
  let cH: class H
  let cM: class M
  let cN: class N
  let vn: setvar n
  let cK: class K
  let cZ: class Z
  assume seqhomo.1: |- ( ( ph /\ ( x e. S /\ y e. S ) ) -> ( x .+ y ) e. S )
  assume seqhomo.2: |- ( ( ph /\ x e. ( M ... N ) ) -> ( F ` x ) e. S )
  assume seqhomo.3: |- ( ph -> N e. ( ZZ>= ` M ) )
  assume seqhomo.4: |- ( ( ph /\ ( x e. S /\ y e. S ) ) -> ( H ` ( x .+ y ) ) = ( ( H ` x ) Q ( H ` y ) ) )
  assume seqhomo.5: |- ( ( ph /\ x e. ( M ... N ) ) -> ( H ` ( F ` x ) ) = ( G ` x ) )

  disjoint x y
  disjoint F x
  disjoint F y
  disjoint H x
  disjoint H y
  disjoint M x
  disjoint M y
  disjoint N x
  disjoint N y
  disjoint ph x
  disjoint ph y
  disjoint G x
  disjoint .+ x
  disjoint .+ y
  disjoint Q x
  disjoint Q y
  disjoint S x
  disjoint S y
  disjoint n x
  disjoint n y
  disjoint F n
  disjoint H n
  disjoint M n
  disjoint N n
  disjoint n ph
  disjoint G n
  disjoint K x
  disjoint K y
  disjoint .+ n
  disjoint Q n
  disjoint Z x
  disjoint Z y
  assert |- ( ph -> ( H ` ( seq M ( .+ , F ) ` N ) ) = ( seq M ( Q , G ) ` N ) )

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
    cH
    cfv
    #
    cN
    cQ
    cG
    cM
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
    seqhomo.3
    cM
    cN
    eluzfz2
    syl
    @9
    wph
    @1
    @7
    wi
    #
    seqhomo.3
    wph
    vx
    cv
    #
    @0
    wcel
    #
    @11
    @2
    cfv
    #
    cH
    cfv
    #
    @11
    @5
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
    cH
    cfv
    #
    cM
    @5
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
    @25
    @2
    cfv
    #
    cH
    cfv
    #
    @25
    @5
    cfv
    #
    wceq
    #
    wi
    #
    wi
    wph
    @25
    c1
    caddc
    co
    #
    @0
    wcel
    #
    @32
    @2
    cfv
    #
    cH
    cfv
    #
    @32
    @5
    cfv
    #
    wceq
    #
    wi
    #
    wi
    wph
    @10
    wi
    vx
    vn
    cM
    cN
    @11
    cM
    wceq
    #
    @17
    @23
    wph
    @39
    @12
    @18
    @16
    @22
    @11
    cM
    @0
    eleq1
    @39
    @14
    @20
    @15
    @21
    @39
    @13
    @19
    cH
    @11
    cM
    @2
    fveq2
    fveq2d
    @11
    cM
    @5
    fveq2
    eqeq12d
    imbi12d
    imbi2d
    @11
    @25
    wceq
    #
    @17
    @31
    wph
    @40
    @12
    @26
    @16
    @30
    @11
    @25
    @0
    eleq1
    @40
    @14
    @28
    @15
    @29
    @40
    @13
    @27
    cH
    @11
    @25
    @2
    fveq2
    fveq2d
    @11
    @25
    @5
    fveq2
    eqeq12d
    imbi12d
    imbi2d
    @11
    @32
    wceq
    #
    @17
    @38
    wph
    @41
    @12
    @33
    @16
    @37
    @11
    @32
    @0
    eleq1
    @41
    @14
    @35
    @15
    @36
    @41
    @13
    @34
    cH
    @11
    @32
    @2
    fveq2
    fveq2d
    @11
    @32
    @5
    fveq2
    eqeq12d
    imbi12d
    imbi2d
    @11
    cN
    wceq
    #
    @17
    @10
    wph
    @42
    @12
    @1
    @16
    @7
    @11
    cN
    @0
    eleq1
    @42
    @14
    @4
    @15
    @6
    @42
    @13
    @3
    cH
    @11
    cN
    @2
    fveq2
    fveq2d
    @11
    cN
    @5
    fveq2
    eqeq12d
    imbi12d
    imbi2d
    @24
    cM
    cz
    wcel
    #
    wph
    @22
    @18
    wph
    cM
    cF
    cfv
    #
    cH
    cfv
    #
    cM
    cG
    cfv
    #
    @20
    @21
    wph
    @18
    @11
    cF
    cfv
    #
    cH
    cfv
    #
    @11
    cG
    cfv
    #
    wceq
    #
    vx
    @0
    wral
    #
    @45
    @46
    wceq
    #
    wph
    @9
    @18
    seqhomo.3
    cM
    cN
    eluzfz1
    syl
    wph
    @50
    vx
    @0
    seqhomo.5
    ralrimiva
    #
    @50
    @52
    vx
    cM
    @0
    @39
    @48
    @45
    @49
    @46
    @39
    @47
    @44
    cH
    @11
    cM
    cF
    fveq2
    fveq2d
    @11
    cM
    cG
    fveq2
    eqeq12d
    rspcv
    sylc
    wph
    @19
    @44
    cH
    wph
    @9
    @43
    @19
    @44
    wceq
    seqhomo.3
    cM
    cN
    eluzel2
    #
    c.pl
    cF
    cM
    seq1
    3syl
    fveq2d
    wph
    @9
    @43
    @21
    @46
    wceq
    seqhomo.3
    @54
    cQ
    cG
    cM
    seq1
    3syl
    3eqtr4d
    a1d
    a1i
    @25
    @8
    wcel
    #
    wph
    @31
    @38
    wph
    @55
    @31
    @38
    wi
    wph
    @55
    wa
    #
    @31
    @33
    @30
    wi
    @38
    @56
    @33
    @26
    @30
    wph
    @55
    @33
    @26
    wph
    @55
    @33
    wa
    #
    wa
    #
    @55
    @33
    @26
    wph
    @55
    @33
    simprl
    #
    wph
    @55
    @33
    simprr
    #
    @25
    cM
    cN
    peano2fzr
    syl2anc
    #
    expr
    imim1d
    @56
    @33
    @30
    @37
    wph
    @55
    @33
    @30
    @37
    wi
    @30
    @37
    @58
    @28
    @32
    cG
    cfv
    #
    cQ
    co
    #
    @29
    @62
    cQ
    co
    #
    wceq
    @28
    @29
    @62
    cQ
    oveq1
    @58
    @35
    @63
    @36
    @64
    @58
    @35
    @27
    @32
    cF
    cfv
    #
    c.pl
    co
    #
    cH
    cfv
    #
    @28
    @65
    cH
    cfv
    #
    cQ
    co
    #
    @63
    @58
    @34
    @66
    cH
    @55
    @34
    @66
    wceq
    wph
    @33
    c.pl
    cF
    cM
    @25
    seqp1
    ad2antrl
    fveq2d
    @58
    @11
    vy
    cv
    #
    c.pl
    co
    #
    cH
    cfv
    #
    @11
    cH
    cfv
    #
    @70
    cH
    cfv
    #
    cQ
    co
    #
    wceq
    #
    vy
    cS
    wral
    vx
    cS
    wral
    #
    @67
    @69
    wceq
    #
    wph
    @77
    @57
    wph
    @76
    vx
    vy
    cS
    cS
    seqhomo.4
    ralrimivva
    adantr
    @58
    @27
    cS
    wcel
    @65
    cS
    wcel
    #
    @77
    @78
    wi
    @58
    vx
    vy
    c.pl
    cS
    cF
    cM
    @25
    @59
    @58
    @11
    cM
    @25
    cfz
    co
    #
    wcel
    @12
    @47
    cS
    wcel
    #
    @58
    @80
    @0
    @11
    @58
    @26
    cN
    @25
    cuz
    cfv
    wcel
    @80
    @0
    wss
    @61
    @25
    cM
    cN
    elfzuz3
    @25
    cM
    cN
    fzss2
    3syl
    sselda
    wph
    @12
    @81
    @57
    seqhomo.2
    adantlr
    syldan
    wph
    @11
    cS
    wcel
    @70
    cS
    wcel
    wa
    @71
    cS
    wcel
    @57
    seqhomo.1
    adantlr
    seqcl
    @58
    @33
    @81
    vx
    @0
    wral
    #
    @79
    @60
    wph
    @82
    @57
    wph
    @81
    vx
    @0
    seqhomo.2
    ralrimiva
    adantr
    @81
    @79
    vx
    @32
    @0
    @41
    @47
    @65
    cS
    @11
    @32
    cF
    fveq2
    #
    eleq1d
    rspcv
    sylc
    @76
    @78
    @27
    @70
    c.pl
    co
    #
    cH
    cfv
    #
    @28
    @74
    cQ
    co
    #
    wceq
    vx
    vy
    @27
    @65
    cS
    cS
    @11
    @27
    wceq
    #
    @72
    @85
    @75
    @86
    @87
    @71
    @84
    cH
    @11
    @27
    @70
    c.pl
    oveq1
    fveq2d
    @87
    @73
    @28
    @74
    cQ
    @11
    @27
    cH
    fveq2
    oveq1d
    eqeq12d
    @70
    @65
    wceq
    #
    @85
    @67
    @86
    @69
    @88
    @84
    @66
    cH
    @70
    @65
    @27
    c.pl
    oveq2
    fveq2d
    @88
    @74
    @68
    @28
    cQ
    @70
    @65
    cH
    fveq2
    oveq2d
    eqeq12d
    rspc2v
    syl2anc
    mpd
    @58
    @68
    @62
    @28
    cQ
    @58
    @33
    @51
    @68
    @62
    wceq
    #
    @60
    wph
    @51
    @57
    @53
    adantr
    @50
    @89
    vx
    @32
    @0
    @41
    @48
    @68
    @49
    @62
    @41
    @47
    @65
    cH
    @83
    fveq2d
    @11
    @32
    cG
    fveq2
    eqeq12d
    rspcv
    sylc
    oveq2d
    3eqtrd
    @55
    @36
    @64
    wceq
    wph
    @33
    cQ
    cG
    cM
    @25
    seqp1
    ad2antrl
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
