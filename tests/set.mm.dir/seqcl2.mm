include "cfz.mm"
include "co.mm"
include "wcel.mm"
include "cseq.mm"
include "cfv.mm"
include "cuz.mm"
include "eluzfz2.mm"
include "syl.mm"
include "wi.mm"
include "cv.mm"
include "c1.mm"
include "caddc.mm"
include "wceq.mm"
include "eleq1.mm"
include "fveq2.mm"
include "eleq1d.mm"
include "imbi12d.mm"
include "imbi2d.mm"
include "cz.mm"
include "seq1.mm"
include "syl5ibr.mm"
include "a1dd.mm"
include "wa.mm"
include "peano2fzr.mm"
include "adantl.mm"
include "expr.mm"
include "imim1d.mm"
include "wral.mm"
include "eluzp1p1.mm"
include "ad2antrl.mm"
include "elfzuz3.mm"
include "ad2antll.mm"
include "elfzuzb.mm"
include "sylanbrc.mm"
include "ralrimiva.mm"
include "adantr.mm"
include "rspcv.mm"
include "sylc.mm"
include "caovclg.mm"
include "ex.mm"
include "mpan2d.mm"
include "seqp1.mm"
include "sylibrd.mm"
include "a2d.mm"
include "syld.mm"
include "expcom.mm"
include "uzind4.mm"
include "mpcom.mm"
include "mpd.mm"

theorem seqcl2
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cC: class C
  let cD: class D
  let c.pl: class .+
  let cF: class F
  let cM: class M
  let cN: class N
  let vk: setvar k
  let vn: setvar n
  assume seqcl2.1: |- ( ph -> ( F ` M ) e. C )
  assume seqcl2.2: |- ( ( ph /\ ( x e. C /\ y e. D ) ) -> ( x .+ y ) e. C )
  assume seqcl2.3: |- ( ph -> N e. ( ZZ>= ` M ) )
  assume seqcl2.4: |- ( ( ph /\ x e. ( ( M + 1 ) ... N ) ) -> ( F ` x ) e. D )

  disjoint x y
  disjoint C x
  disjoint C y
  disjoint D x
  disjoint D y
  disjoint F x
  disjoint F y
  disjoint M x
  disjoint M y
  disjoint N x
  disjoint .+ x
  disjoint .+ y
  disjoint ph x
  disjoint ph y
  disjoint k n
  disjoint k x
  disjoint k y
  disjoint C k
  disjoint n x
  disjoint n y
  disjoint C n
  disjoint F k
  disjoint F n
  disjoint M k
  disjoint M n
  disjoint N n
  disjoint .+ k
  disjoint .+ n
  disjoint k ph
  disjoint n ph
  assert |- ( ph -> ( seq M ( .+ , F ) ` N ) e. C )

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
    cC
    wcel
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
    seqcl2.3
    cM
    cN
    eluzfz2
    syl
    @6
    wph
    @1
    @4
    wi
    #
    seqcl2.3
    wph
    vx
    cv
    #
    @0
    wcel
    #
    @8
    @2
    cfv
    #
    cC
    wcel
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
    cC
    wcel
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
    @17
    @2
    cfv
    #
    cC
    wcel
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
    @22
    @2
    cfv
    #
    cC
    wcel
    #
    wi
    #
    wi
    wph
    @7
    wi
    vx
    vn
    cM
    cN
    @8
    cM
    wceq
    #
    @12
    @16
    wph
    @27
    @9
    @13
    @11
    @15
    @8
    cM
    @0
    eleq1
    @27
    @10
    @14
    cC
    @8
    cM
    @2
    fveq2
    eleq1d
    imbi12d
    imbi2d
    @8
    @17
    wceq
    #
    @12
    @21
    wph
    @28
    @9
    @18
    @11
    @20
    @8
    @17
    @0
    eleq1
    @28
    @10
    @19
    cC
    @8
    @17
    @2
    fveq2
    eleq1d
    imbi12d
    imbi2d
    @8
    @22
    wceq
    #
    @12
    @26
    wph
    @29
    @9
    @23
    @11
    @25
    @8
    @22
    @0
    eleq1
    @29
    @10
    @24
    cC
    @8
    @22
    @2
    fveq2
    eleq1d
    imbi12d
    imbi2d
    @8
    cN
    wceq
    #
    @12
    @7
    wph
    @30
    @9
    @1
    @11
    @4
    @8
    cN
    @0
    eleq1
    @30
    @10
    @3
    cC
    @8
    cN
    @2
    fveq2
    eleq1d
    imbi12d
    imbi2d
    cM
    cz
    wcel
    #
    wph
    @15
    @13
    wph
    @15
    @31
    cM
    cF
    cfv
    #
    cC
    wcel
    seqcl2.1
    @31
    @14
    @32
    cC
    c.pl
    cF
    cM
    seq1
    eleq1d
    syl5ibr
    a1dd
    @17
    @5
    wcel
    #
    wph
    @21
    @26
    wph
    @33
    @21
    @26
    wi
    wph
    @33
    wa
    #
    @21
    @23
    @20
    wi
    @26
    @34
    @23
    @18
    @20
    wph
    @33
    @23
    @18
    @33
    @23
    wa
    #
    @18
    wph
    @17
    cM
    cN
    peano2fzr
    adantl
    expr
    imim1d
    @34
    @23
    @20
    @25
    wph
    @33
    @23
    @20
    @25
    wi
    wph
    @35
    wa
    #
    @20
    @19
    @22
    cF
    cfv
    #
    c.pl
    co
    #
    cC
    wcel
    #
    @25
    @36
    @20
    @37
    cD
    wcel
    #
    @39
    @36
    @22
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
    @8
    cF
    cfv
    #
    cD
    wcel
    #
    vx
    @42
    wral
    #
    @40
    @36
    @22
    @41
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
    @43
    @33
    @47
    wph
    @23
    cM
    @17
    eluzp1p1
    ad2antrl
    @23
    @48
    wph
    @33
    @22
    cM
    cN
    elfzuz3
    ad2antll
    @22
    @41
    cN
    elfzuzb
    sylanbrc
    wph
    @46
    @35
    wph
    @45
    vx
    @42
    seqcl2.4
    ralrimiva
    adantr
    @45
    @40
    vx
    @22
    @42
    @29
    @44
    @37
    cD
    @8
    @22
    cF
    fveq2
    eleq1d
    rspcv
    sylc
    wph
    @20
    @40
    wa
    #
    @39
    wi
    @35
    wph
    @49
    @39
    wph
    vx
    vy
    @19
    @37
    cC
    cD
    cC
    c.pl
    seqcl2.2
    caovclg
    ex
    adantr
    mpan2d
    @36
    @24
    @38
    cC
    @33
    @24
    @38
    wceq
    wph
    @23
    c.pl
    cF
    cM
    @17
    seqp1
    ad2antrl
    eleq1d
    sylibrd
    expr
    a2d
    syld
    expcom
    a2d
    uzind4
    mpcom
    mpd
end
