include "wceq.mm"
include "cseq.mm"
include "cfv.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cuz.mm"
include "wcel.mm"
include "cz.mm"
include "eluzelz.mm"
include "seq1.mm"
include "3syl.mm"
include "seqeq1.mm"
include "fveq1d.mm"
include "eqeq1d.mm"
include "syl5ibcom.mm"
include "wa.mm"
include "cmin.mm"
include "eluzel2.mm"
include "syl.mm"
include "seqm1.mm"
include "sylan.mm"
include "cv.mm"
include "wral.mm"
include "ralrimiva.mm"
include "oveq2.mm"
include "id.mm"
include "eqeq12d.mm"
include "rspcv.mm"
include "sylc.mm"
include "adantr.mm"
include "eluzp1m1.mm"
include "cfz.mm"
include "adantlr.mm"
include "seqid3.mm"
include "oveq1d.mm"
include "3eqtrd.mm"
include "ex.mm"
include "wo.mm"
include "uzp1.mm"
include "mpjaod.mm"
include "eqidd.mm"
include "seqfeq2.mm"

theorem seqid
  let wph: wff ph
  let vx: setvar x
  let c.pl: class .+
  let cS: class S
  let cF: class F
  let cM: class M
  let cN: class N
  let cZ: class Z
  assume seqid.1: |- ( ( ph /\ x e. S ) -> ( Z .+ x ) = x )
  assume seqid.2: |- ( ph -> Z e. S )
  assume seqid.3: |- ( ph -> N e. ( ZZ>= ` M ) )
  assume seqid.4: |- ( ph -> ( F ` N ) e. S )
  assume seqid.5: |- ( ( ph /\ x e. ( M ... ( N - 1 ) ) ) -> ( F ` x ) = Z )

  disjoint .+ x
  disjoint F x
  disjoint M x
  disjoint N x
  disjoint S x
  disjoint Z x
  disjoint ph x
  assert |- ( ph -> ( seq M ( .+ , F ) |` ( ZZ>= ` N ) ) = seq N ( .+ , F ) )

  proof
    wph
    c.pl
    vx
    cF
    cF
    cN
    cM
    seqid.3
    wph
    cN
    cM
    wceq
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
    cF
    cfv
    #
    wceq
    #
    cN
    cM
    c1
    caddc
    co
    cuz
    cfv
    wcel
    #
    wph
    cN
    c.pl
    cF
    cN
    cseq
    #
    cfv
    #
    @3
    wceq
    #
    @0
    @4
    wph
    cN
    cM
    cuz
    cfv
    #
    wcel
    #
    cN
    cz
    wcel
    @8
    seqid.3
    cM
    cN
    eluzelz
    c.pl
    cF
    cN
    seq1
    3syl
    @0
    @7
    @2
    @3
    @0
    cN
    @6
    @1
    c.pl
    cF
    cN
    cM
    seqeq1
    fveq1d
    eqeq1d
    syl5ibcom
    wph
    @5
    @4
    wph
    @5
    wa
    #
    @2
    cN
    c1
    cmin
    co
    #
    @1
    cfv
    #
    @3
    c.pl
    co
    #
    cZ
    @3
    c.pl
    co
    #
    @3
    wph
    cM
    cz
    wcel
    #
    @5
    @2
    @14
    wceq
    wph
    @10
    @16
    seqid.3
    cM
    cN
    eluzel2
    syl
    #
    c.pl
    cF
    cM
    cN
    seqm1
    sylan
    @11
    @13
    cZ
    @3
    c.pl
    @11
    vx
    c.pl
    cF
    cM
    @12
    cZ
    wph
    cZ
    cZ
    c.pl
    co
    #
    cZ
    wceq
    #
    @5
    wph
    cZ
    cS
    wcel
    cZ
    vx
    cv
    #
    c.pl
    co
    #
    @20
    wceq
    #
    vx
    cS
    wral
    #
    @19
    seqid.2
    wph
    @22
    vx
    cS
    seqid.1
    ralrimiva
    #
    @22
    @19
    vx
    cZ
    cS
    @20
    cZ
    wceq
    #
    @21
    @18
    @20
    cZ
    @20
    cZ
    cZ
    c.pl
    oveq2
    @25
    id
    eqeq12d
    rspcv
    sylc
    adantr
    wph
    @16
    @5
    @12
    @9
    wcel
    @17
    cM
    cN
    eluzp1m1
    sylan
    wph
    @20
    cM
    @12
    cfz
    co
    wcel
    @20
    cF
    cfv
    #
    cZ
    wceq
    @5
    seqid.5
    adantlr
    seqid3
    oveq1d
    @11
    @3
    cS
    wcel
    #
    @23
    @15
    @3
    wceq
    #
    wph
    @27
    @5
    seqid.4
    adantr
    wph
    @23
    @5
    @24
    adantr
    @22
    @28
    vx
    @3
    cS
    @20
    @3
    wceq
    #
    @21
    @15
    @20
    @3
    @20
    @3
    cZ
    c.pl
    oveq2
    @29
    id
    eqeq12d
    rspcv
    sylc
    3eqtrd
    ex
    wph
    @10
    @0
    @5
    wo
    seqid.3
    cM
    cN
    uzp1
    syl
    mpjaod
    wph
    @20
    cN
    c1
    caddc
    co
    cuz
    cfv
    wcel
    wa
    @26
    eqidd
    seqfeq2
end
