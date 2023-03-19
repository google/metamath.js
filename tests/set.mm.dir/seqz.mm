include "cseq.mm"
include "cfv.mm"
include "cfz.mm"
include "co.mm"
include "wcel.mm"
include "cuz.mm"
include "elfzuz.mm"
include "syl.mm"
include "wceq.mm"
include "c1.mm"
include "caddc.mm"
include "cz.mm"
include "eluzelz.mm"
include "seq1.mm"
include "eqtrd.mm"
include "seqeq1.mm"
include "fveq1d.mm"
include "eqeq1d.mm"
include "syl5ibcom.mm"
include "wa.mm"
include "cmin.mm"
include "eluzel2.mm"
include "seqm1.mm"
include "sylan.mm"
include "adantr.mm"
include "oveq2d.mm"
include "cv.mm"
include "wral.mm"
include "eluzp1m1.mm"
include "wss.mm"
include "fzssp1.mm"
include "cc.mm"
include "zcnd.mm"
include "ax-1cn.mm"
include "npcan.mm"
include "sylancl.mm"
include "syl5sseq.mm"
include "elfzuz3.mm"
include "fzss2.mm"
include "sstrd.mm"
include "sselda.mm"
include "adantlr.mm"
include "syldan.mm"
include "seqcl.mm"
include "ralrimiva.mm"
include "oveq1.mm"
include "rspcv.mm"
include "sylc.mm"
include "ex.mm"
include "wo.mm"
include "uzp1.mm"
include "mpjaod.mm"
include "eqtr4d.mm"
include "eqidd.mm"
include "seqfveq2.mm"
include "csn.mm"
include "fvex.mm"
include "elsn.mm"
include "sylibr.mm"
include "simprl.mm"
include "velsn.mm"
include "sylib.mm"
include "oveq1d.mm"
include "simprr.mm"
include "oveq2.mm"
include "ovex.mm"
include "peano2uz.mm"
include "fzss1.mm"
include "seqcl2.mm"
include "elsni.mm"

theorem seqz
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let c.pl: class .+
  let cS: class S
  let cF: class F
  let cK: class K
  let cM: class M
  let cN: class N
  let cV: class V
  let cZ: class Z
  let vn: setvar n
  let cH: class H
  let cG: class G
  let cQ: class Q
  assume seqhomo.1: |- ( ( ph /\ ( x e. S /\ y e. S ) ) -> ( x .+ y ) e. S )
  assume seqhomo.2: |- ( ( ph /\ x e. ( M ... N ) ) -> ( F ` x ) e. S )
  assume seqz.3: |- ( ( ph /\ x e. S ) -> ( Z .+ x ) = Z )
  assume seqz.4: |- ( ( ph /\ x e. S ) -> ( x .+ Z ) = Z )
  assume seqz.5: |- ( ph -> K e. ( M ... N ) )
  assume seqz.6: |- ( ph -> N e. V )
  assume seqz.7: |- ( ph -> ( F ` K ) = Z )

  disjoint x y
  disjoint F x
  disjoint F y
  disjoint M x
  disjoint M y
  disjoint N x
  disjoint N y
  disjoint ph x
  disjoint ph y
  disjoint K x
  disjoint K y
  disjoint .+ x
  disjoint .+ y
  disjoint S x
  disjoint S y
  disjoint Z x
  disjoint Z y
  disjoint n x
  disjoint n y
  disjoint F n
  disjoint H n
  disjoint H x
  disjoint H y
  disjoint M n
  disjoint N n
  disjoint n ph
  disjoint G n
  disjoint G x
  disjoint .+ n
  disjoint Q n
  disjoint Q x
  disjoint Q y
  assert |- ( ph -> ( seq M ( .+ , F ) ` N ) = Z )

  proof
    wph
    cN
    c.pl
    cF
    cM
    cseq
    #
    cfv
    cN
    c.pl
    cF
    cK
    cseq
    #
    cfv
    #
    cZ
    wph
    c.pl
    vx
    cF
    cF
    cK
    cM
    cN
    wph
    cK
    cM
    cN
    cfz
    co
    #
    wcel
    #
    cK
    cM
    cuz
    cfv
    #
    wcel
    #
    seqz.5
    cK
    cM
    cN
    elfzuz
    syl
    #
    wph
    cK
    @0
    cfv
    #
    cZ
    cK
    cF
    cfv
    #
    wph
    cK
    cM
    wceq
    #
    @8
    cZ
    wceq
    #
    cK
    cM
    c1
    caddc
    co
    cuz
    cfv
    wcel
    #
    wph
    cK
    @1
    cfv
    #
    cZ
    wceq
    @10
    @11
    wph
    @13
    @9
    cZ
    wph
    cK
    cz
    wcel
    #
    @13
    @9
    wceq
    wph
    @6
    @14
    @7
    cM
    cK
    eluzelz
    syl
    #
    c.pl
    cF
    cK
    seq1
    syl
    seqz.7
    eqtrd
    @10
    @13
    @8
    cZ
    @10
    cK
    @1
    @0
    c.pl
    cF
    cK
    cM
    seqeq1
    fveq1d
    eqeq1d
    syl5ibcom
    wph
    @12
    @11
    wph
    @12
    wa
    #
    @8
    cK
    c1
    cmin
    co
    #
    @0
    cfv
    #
    @9
    c.pl
    co
    #
    cZ
    wph
    cM
    cz
    wcel
    #
    @12
    @8
    @19
    wceq
    wph
    @6
    @20
    @7
    cM
    cK
    eluzel2
    syl
    #
    c.pl
    cF
    cM
    cK
    seqm1
    sylan
    @16
    @19
    @18
    cZ
    c.pl
    co
    #
    cZ
    @16
    @9
    cZ
    @18
    c.pl
    wph
    @9
    cZ
    wceq
    #
    @12
    seqz.7
    adantr
    oveq2d
    @16
    @18
    cS
    wcel
    vx
    cv
    #
    cZ
    c.pl
    co
    #
    cZ
    wceq
    #
    vx
    cS
    wral
    #
    @22
    cZ
    wceq
    #
    @16
    vx
    vy
    c.pl
    cS
    cF
    cM
    @17
    wph
    @20
    @12
    @17
    @5
    wcel
    @21
    cM
    cK
    eluzp1m1
    sylan
    @16
    @24
    cM
    @17
    cfz
    co
    #
    wcel
    @24
    @3
    wcel
    #
    @24
    cF
    cfv
    #
    cS
    wcel
    #
    @16
    @29
    @3
    @24
    wph
    @29
    @3
    wss
    @12
    wph
    @29
    cM
    cK
    cfz
    co
    #
    @3
    wph
    cM
    @17
    c1
    caddc
    co
    #
    cfz
    co
    @29
    @33
    cM
    @17
    fzssp1
    wph
    @34
    cK
    cM
    cfz
    wph
    cK
    cc
    wcel
    c1
    cc
    wcel
    @34
    cK
    wceq
    wph
    cK
    @15
    zcnd
    ax-1cn
    cK
    c1
    npcan
    sylancl
    oveq2d
    syl5sseq
    wph
    cN
    cK
    cuz
    cfv
    wcel
    #
    @33
    @3
    wss
    wph
    @4
    @35
    seqz.5
    cK
    cM
    cN
    elfzuz3
    syl
    #
    cK
    cM
    cN
    fzss2
    syl
    sstrd
    adantr
    sselda
    wph
    @30
    @32
    @12
    seqhomo.2
    adantlr
    syldan
    wph
    @24
    cS
    wcel
    vy
    cv
    #
    cS
    wcel
    #
    wa
    @24
    @37
    c.pl
    co
    #
    cS
    wcel
    @12
    seqhomo.1
    adantlr
    seqcl
    wph
    @27
    @12
    wph
    @26
    vx
    cS
    seqz.4
    ralrimiva
    adantr
    @26
    @28
    vx
    @18
    cS
    @24
    @18
    wceq
    @25
    @22
    cZ
    @24
    @18
    cZ
    c.pl
    oveq1
    eqeq1d
    rspcv
    sylc
    eqtrd
    eqtrd
    ex
    wph
    @6
    @10
    @12
    wo
    @7
    cM
    cK
    uzp1
    syl
    mpjaod
    seqz.7
    eqtr4d
    @36
    wph
    @24
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
    wa
    @31
    eqidd
    seqfveq2
    wph
    @2
    cZ
    csn
    #
    wcel
    @2
    cZ
    wceq
    wph
    vx
    vy
    @43
    cS
    c.pl
    cF
    cK
    cN
    wph
    @23
    @9
    @43
    wcel
    seqz.7
    @9
    cZ
    cK
    cF
    fvex
    elsn
    sylibr
    wph
    @24
    @43
    wcel
    #
    @38
    wa
    #
    wa
    #
    @39
    cZ
    wceq
    @39
    @43
    wcel
    @46
    @39
    cZ
    @37
    c.pl
    co
    #
    cZ
    @46
    @24
    cZ
    @37
    c.pl
    @46
    @44
    @24
    cZ
    wceq
    wph
    @44
    @38
    simprl
    vx
    cZ
    velsn
    sylib
    oveq1d
    @46
    @38
    cZ
    @24
    c.pl
    co
    #
    cZ
    wceq
    #
    vx
    cS
    wral
    #
    @47
    cZ
    wceq
    #
    wph
    @44
    @38
    simprr
    wph
    @50
    @45
    wph
    @49
    vx
    cS
    seqz.3
    ralrimiva
    adantr
    @49
    @51
    vx
    @37
    cS
    @24
    @37
    wceq
    @48
    @47
    cZ
    @24
    @37
    cZ
    c.pl
    oveq2
    eqeq1d
    rspcv
    sylc
    eqtrd
    @39
    cZ
    @24
    @37
    c.pl
    ovex
    elsn
    sylibr
    @36
    wph
    @42
    @30
    @32
    wph
    @41
    @3
    @24
    wph
    @40
    @5
    wcel
    #
    @41
    @3
    wss
    wph
    @6
    @52
    @7
    cM
    cK
    peano2uz
    syl
    @40
    cM
    cN
    fzss1
    syl
    sselda
    seqhomo.2
    syldan
    seqcl2
    @2
    cZ
    elsni
    syl
    eqtrd
end
