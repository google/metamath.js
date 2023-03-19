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
include "eqeq2d.mm"
include "imbi12d.mm"
include "imbi2d.mm"
include "cz.mm"
include "eqidd.mm"
include "2a1i.mm"
include "wa.mm"
include "peano2fzr.mm"
include "adantl.mm"
include "expr.mm"
include "imim1d.mm"
include "oveq1.mm"
include "wral.mm"
include "eluzp1p1.mm"
include "ad2antrl.mm"
include "elfzuz3.mm"
include "ad2antll.mm"
include "elfzuzb.mm"
include "sylanbrc.mm"
include "ralrimiva.mm"
include "adantr.mm"
include "eqeq1d.mm"
include "rspcv.mm"
include "sylc.mm"
include "oveq2d.mm"
include "id.mm"
include "eqeq12d.mm"
include "eqtr2d.mm"
include "simprl.mm"
include "uztrn.mm"
include "syl2anc.mm"
include "seqp1.mm"
include "syl5ibr.mm"
include "a2d.mm"
include "syld.mm"
include "expcom.mm"
include "uzind4.mm"
include "mpcom.mm"
include "mpd.mm"

theorem seqid2
  let wph: wff ph
  let vx: setvar x
  let c.pl: class .+
  let cS: class S
  let cF: class F
  let cK: class K
  let cM: class M
  let cN: class N
  let cZ: class Z
  let vn: setvar n
  assume seqid2.1: |- ( ( ph /\ x e. S ) -> ( x .+ Z ) = x )
  assume seqid2.2: |- ( ph -> K e. ( ZZ>= ` M ) )
  assume seqid2.3: |- ( ph -> N e. ( ZZ>= ` K ) )
  assume seqid2.4: |- ( ph -> ( seq M ( .+ , F ) ` K ) e. S )
  assume seqid2.5: |- ( ( ph /\ x e. ( ( K + 1 ) ... N ) ) -> ( F ` x ) = Z )

  disjoint F x
  disjoint K x
  disjoint M x
  disjoint N x
  disjoint ph x
  disjoint S x
  disjoint .+ x
  disjoint Z x
  disjoint n x
  disjoint F n
  disjoint K n
  disjoint M n
  disjoint N n
  disjoint n ph
  disjoint .+ n
  assert |- ( ph -> ( seq M ( .+ , F ) ` K ) = ( seq M ( .+ , F ) ` N ) )

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
    cK
    c.pl
    cF
    cM
    cseq
    #
    cfv
    #
    cN
    @2
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
    seqid2.3
    cK
    cN
    eluzfz2
    syl
    @7
    wph
    @1
    @5
    wi
    #
    seqid2.3
    wph
    vx
    cv
    #
    @0
    wcel
    #
    @3
    @9
    @2
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
    @3
    @3
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
    @3
    @17
    @2
    cfv
    #
    wceq
    #
    wi
    #
    wi
    wph
    @17
    c1
    caddc
    co
    #
    @0
    wcel
    #
    @3
    @22
    @2
    cfv
    #
    wceq
    #
    wi
    #
    wi
    wph
    @8
    wi
    vx
    vn
    cK
    cN
    @9
    cK
    wceq
    #
    @13
    @16
    wph
    @27
    @10
    @14
    @12
    @15
    @9
    cK
    @0
    eleq1
    @27
    @11
    @3
    @3
    @9
    cK
    @2
    fveq2
    eqeq2d
    imbi12d
    imbi2d
    @9
    @17
    wceq
    #
    @13
    @21
    wph
    @28
    @10
    @18
    @12
    @20
    @9
    @17
    @0
    eleq1
    @28
    @11
    @19
    @3
    @9
    @17
    @2
    fveq2
    eqeq2d
    imbi12d
    imbi2d
    @9
    @22
    wceq
    #
    @13
    @26
    wph
    @29
    @10
    @23
    @12
    @25
    @9
    @22
    @0
    eleq1
    @29
    @11
    @24
    @3
    @9
    @22
    @2
    fveq2
    eqeq2d
    imbi12d
    imbi2d
    @9
    cN
    wceq
    #
    @13
    @8
    wph
    @30
    @10
    @1
    @12
    @5
    @9
    cN
    @0
    eleq1
    @30
    @11
    @4
    @3
    @9
    cN
    @2
    fveq2
    eqeq2d
    imbi12d
    imbi2d
    @16
    cK
    cz
    wcel
    wph
    @14
    @3
    eqidd
    2a1i
    @17
    @6
    wcel
    #
    wph
    @21
    @26
    wph
    @31
    @21
    @26
    wi
    wph
    @31
    wa
    #
    @21
    @23
    @20
    wi
    @26
    @32
    @23
    @18
    @20
    wph
    @31
    @23
    @18
    @31
    @23
    wa
    #
    @18
    wph
    @17
    cK
    cN
    peano2fzr
    adantl
    expr
    imim1d
    @32
    @23
    @20
    @25
    wph
    @31
    @23
    @20
    @25
    wi
    @20
    @25
    wph
    @33
    wa
    #
    @3
    @22
    cF
    cfv
    #
    c.pl
    co
    #
    @19
    @35
    c.pl
    co
    #
    wceq
    @3
    @19
    @35
    c.pl
    oveq1
    @34
    @3
    @36
    @24
    @37
    @34
    @36
    @3
    cZ
    c.pl
    co
    #
    @3
    @34
    @35
    cZ
    @3
    c.pl
    @34
    @22
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
    @9
    cF
    cfv
    #
    cZ
    wceq
    #
    vx
    @40
    wral
    #
    @35
    cZ
    wceq
    #
    @34
    @22
    @39
    cuz
    cfv
    wcel
    #
    cN
    @22
    cuz
    cfv
    wcel
    #
    @41
    @31
    @46
    wph
    @23
    cK
    @17
    eluzp1p1
    ad2antrl
    @23
    @47
    wph
    @31
    @22
    cK
    cN
    elfzuz3
    ad2antll
    @22
    @39
    cN
    elfzuzb
    sylanbrc
    wph
    @44
    @33
    wph
    @43
    vx
    @40
    seqid2.5
    ralrimiva
    adantr
    @43
    @45
    vx
    @22
    @40
    @29
    @42
    @35
    cZ
    @9
    @22
    cF
    fveq2
    eqeq1d
    rspcv
    sylc
    oveq2d
    wph
    @38
    @3
    wceq
    #
    @33
    wph
    @3
    cS
    wcel
    @9
    cZ
    c.pl
    co
    #
    @9
    wceq
    #
    vx
    cS
    wral
    @48
    seqid2.4
    wph
    @50
    vx
    cS
    seqid2.1
    ralrimiva
    @50
    @48
    vx
    @3
    cS
    @9
    @3
    wceq
    #
    @49
    @38
    @9
    @3
    @9
    @3
    cZ
    c.pl
    oveq1
    @51
    id
    eqeq12d
    rspcv
    sylc
    adantr
    eqtr2d
    @34
    @17
    cM
    cuz
    cfv
    #
    wcel
    #
    @24
    @37
    wceq
    @34
    @31
    cK
    @52
    wcel
    #
    @53
    wph
    @31
    @23
    simprl
    wph
    @54
    @33
    seqid2.2
    adantr
    cK
    @17
    cM
    uztrn
    syl2anc
    c.pl
    cF
    cM
    @17
    seqp1
    syl
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
