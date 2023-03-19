include "caddc.mm"
include "cseq.mm"
include "cv.mm"
include "cfz.mm"
include "co.mm"
include "wcel.mm"
include "wa.mm"
include "cr.mm"
include "cuz.mm"
include "cfv.mm"
include "elfzuz.mm"
include "uztrn.mm"
include "syl2anr.mm"
include "wss.mm"
include "elfzuz3.mm"
include "adantl.mm"
include "fzss2.mm"
include "syl.mm"
include "sselda.mm"
include "adantlr.mm"
include "syldan.mm"
include "readdcl.mm"
include "seqcl.mm"
include "c1.mm"
include "cmin.mm"
include "cle.mm"
include "cc0.mm"
include "wbr.mm"
include "wral.mm"
include "simpr.mm"
include "cz.mm"
include "wb.mm"
include "adantr.mm"
include "eluzelz.mm"
include "peano2zm.mm"
include "elfzelz.mm"
include "1zzd.mm"
include "fzaddel.mm"
include "syl22anc.mm"
include "mpbid.mm"
include "wceq.mm"
include "cc.mm"
include "zcn.mm"
include "ax-1cn.mm"
include "npcan.mm"
include "sylancl.mm"
include "oveq2d.mm"
include "eleqtrd.mm"
include "ralrimiva.mm"
include "fveq2.mm"
include "breq2d.mm"
include "rspcv.mm"
include "sylc.mm"
include "fzelp1.mm"
include "fzss1.mm"
include "fzp1elp1.mm"
include "sseldd.mm"
include "eleq1d.mm"
include "addge01d.mm"
include "seqp1.mm"
include "breqtrrd.mm"
include "monoord.mm"

theorem sermono
  let wph: wff ph
  let vx: setvar x
  let cF: class F
  let cK: class K
  let cM: class M
  let cN: class N
  let vk: setvar k
  let vy: setvar y
  assume sermono.1: |- ( ph -> K e. ( ZZ>= ` M ) )
  assume sermono.2: |- ( ph -> N e. ( ZZ>= ` K ) )
  assume sermono.3: |- ( ( ph /\ x e. ( M ... N ) ) -> ( F ` x ) e. RR )
  assume sermono.4: |- ( ( ph /\ x e. ( ( K + 1 ) ... N ) ) -> 0 <_ ( F ` x ) )

  disjoint F x
  disjoint K x
  disjoint M x
  disjoint N x
  disjoint ph x
  disjoint k x
  disjoint k y
  disjoint F k
  disjoint x y
  disjoint F y
  disjoint K k
  disjoint K y
  disjoint M k
  disjoint M y
  disjoint N k
  disjoint N y
  disjoint k ph
  disjoint ph y
  assert |- ( ph -> ( seq M ( + , F ) ` K ) <_ ( seq M ( + , F ) ` N ) )

  proof
    wph
    vk
    caddc
    cF
    cM
    cseq
    #
    cK
    cN
    sermono.2
    wph
    vk
    cv
    #
    cK
    cN
    cfz
    co
    #
    wcel
    #
    wa
    #
    vx
    vy
    caddc
    cr
    cF
    cM
    @1
    @3
    @1
    cK
    cuz
    cfv
    #
    wcel
    cK
    cM
    cuz
    cfv
    #
    wcel
    #
    @1
    @6
    wcel
    #
    wph
    @1
    cK
    cN
    elfzuz
    sermono.1
    cK
    @1
    cM
    uztrn
    syl2anr
    #
    @4
    vx
    cv
    #
    cM
    @1
    cfz
    co
    #
    wcel
    @10
    cM
    cN
    cfz
    co
    #
    wcel
    #
    @10
    cF
    cfv
    #
    cr
    wcel
    #
    @4
    @11
    @12
    @10
    @4
    cN
    @1
    cuz
    cfv
    wcel
    #
    @11
    @12
    wss
    @3
    @16
    wph
    @1
    cK
    cN
    elfzuz3
    adantl
    @1
    cM
    cN
    fzss2
    syl
    sselda
    wph
    @13
    @15
    @3
    sermono.3
    adantlr
    syldan
    @10
    cr
    wcel
    vy
    cv
    #
    cr
    wcel
    wa
    @10
    @17
    caddc
    co
    cr
    wcel
    @4
    @10
    @17
    readdcl
    adantl
    seqcl
    #
    wph
    @1
    cK
    cN
    c1
    cmin
    co
    #
    cfz
    co
    wcel
    #
    wa
    #
    @1
    @0
    cfv
    #
    @22
    @1
    c1
    caddc
    co
    #
    cF
    cfv
    #
    caddc
    co
    #
    @23
    @0
    cfv
    #
    cle
    @21
    cc0
    @24
    cle
    wbr
    #
    @22
    @25
    cle
    wbr
    @21
    @23
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
    cc0
    @14
    cle
    wbr
    #
    vx
    @29
    wral
    #
    @27
    @21
    @23
    @28
    @19
    c1
    caddc
    co
    #
    cfz
    co
    #
    @29
    @21
    @20
    @23
    @33
    wcel
    #
    wph
    @20
    simpr
    @21
    cK
    cz
    wcel
    #
    @19
    cz
    wcel
    #
    @1
    cz
    wcel
    #
    c1
    cz
    wcel
    @20
    @34
    wb
    @21
    @7
    @35
    wph
    @7
    @20
    sermono.1
    adantr
    #
    cM
    cK
    eluzelz
    syl
    @21
    cN
    cz
    wcel
    #
    @36
    @21
    cN
    @5
    wcel
    #
    @39
    wph
    @40
    @20
    sermono.2
    adantr
    cK
    cN
    eluzelz
    syl
    #
    cN
    peano2zm
    syl
    @20
    @37
    wph
    @1
    cK
    @19
    elfzelz
    adantl
    @21
    1zzd
    @1
    c1
    cK
    @19
    fzaddel
    syl22anc
    mpbid
    @21
    @32
    cN
    @28
    cfz
    @21
    @39
    @32
    cN
    wceq
    #
    @41
    @39
    cN
    cc
    wcel
    c1
    cc
    wcel
    @42
    cN
    zcn
    ax-1cn
    cN
    c1
    npcan
    sylancl
    syl
    #
    oveq2d
    eleqtrd
    wph
    @31
    @20
    wph
    @30
    vx
    @29
    sermono.4
    ralrimiva
    adantr
    @30
    @27
    vx
    @23
    @29
    @10
    @23
    wceq
    #
    @14
    @24
    cc0
    cle
    @10
    @23
    cF
    fveq2
    #
    breq2d
    rspcv
    sylc
    @21
    @22
    @24
    wph
    @20
    @3
    @22
    cr
    wcel
    @21
    @1
    cK
    @32
    cfz
    co
    #
    @2
    @20
    @1
    @46
    wcel
    wph
    @1
    cK
    @19
    fzelp1
    adantl
    @21
    @32
    cN
    cK
    cfz
    @43
    oveq2d
    #
    eleqtrd
    #
    @18
    syldan
    @21
    @23
    @12
    wcel
    @15
    vx
    @12
    wral
    #
    @24
    cr
    wcel
    #
    @21
    @2
    @12
    @23
    @21
    @7
    @2
    @12
    wss
    @38
    cK
    cM
    cN
    fzss1
    syl
    @21
    @23
    @46
    @2
    @20
    @23
    @46
    wcel
    wph
    @1
    cK
    @19
    fzp1elp1
    adantl
    @47
    eleqtrd
    sseldd
    wph
    @49
    @20
    wph
    @15
    vx
    @12
    sermono.3
    ralrimiva
    adantr
    @15
    @50
    vx
    @23
    @12
    @44
    @14
    @24
    cr
    @45
    eleq1d
    rspcv
    sylc
    addge01d
    mpbid
    @21
    @8
    @26
    @25
    wceq
    wph
    @20
    @3
    @8
    @48
    @9
    syldan
    caddc
    cF
    cM
    @1
    seqp1
    syl
    breqtrrd
    monoord
end
