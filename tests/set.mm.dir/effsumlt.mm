include "caddc.mm"
include "cc0.mm"
include "cseq.mm"
include "cfv.mm"
include "c1.mm"
include "co.mm"
include "cuz.mm"
include "cv.mm"
include "csu.mm"
include "ce.mm"
include "clt.mm"
include "cn0.mm"
include "cr.mm"
include "nn0uz.mm"
include "0zd.mm"
include "wcel.mm"
include "wa.mm"
include "cexp.mm"
include "cfa.mm"
include "cdiv.mm"
include "wceq.mm"
include "eftval.mm"
include "adantl.mm"
include "rpred.mm"
include "reeftcl.mm"
include "sylan.mm"
include "eqeltrd.mm"
include "serfre.mm"
include "ffvelrnd.mm"
include "eqid.mm"
include "peano2nn0.mm"
include "syl.mm"
include "eqidd.mm"
include "crp.mm"
include "cz.mm"
include "nn0z.mm"
include "rpexpcl.mm"
include "syl2an.mm"
include "cn.mm"
include "faccl.mm"
include "nnrpd.mm"
include "rpdivcld.mm"
include "cc.mm"
include "cli.mm"
include "cdm.mm"
include "recnd.mm"
include "efcllem.mm"
include "isumrpcl.mm"
include "ltaddrpd.mm"
include "cmin.mm"
include "cfz.mm"
include "efval2.mm"
include "isumsplit.mm"
include "nn0cnd.mm"
include "ax-1cn.mm"
include "pncan.mm"
include "sylancl.mm"
include "oveq2d.mm"
include "sumeq1d.mm"
include "syl6eleq.mm"
include "elfznn0.mm"
include "sylan2.mm"
include "fsumser.mm"
include "eqtrd.mm"
include "oveq1d.mm"
include "3eqtrd.mm"
include "breqtrrd.mm"

theorem effsumlt
  let wph: wff ph
  let cA: class A
  let vn: setvar n
  let cF: class F
  let cN: class N
  let vk: setvar k
  assume effsumlt.1: |- F = ( n e. NN0 |-> ( ( A ^ n ) / ( ! ` n ) ) )
  assume effsumlt.2: |- ( ph -> A e. RR+ )
  assume effsumlt.3: |- ( ph -> N e. NN0 )

  disjoint A n
  disjoint k n
  disjoint A k
  disjoint F k
  disjoint N k
  disjoint k ph
  assert |- ( ph -> ( seq 0 ( + , F ) ` N ) < ( exp ` A ) )

  proof
    wph
    cN
    caddc
    cF
    cc0
    cseq
    #
    cfv
    #
    @1
    cN
    c1
    caddc
    co
    #
    cuz
    cfv
    #
    vk
    cv
    #
    cF
    cfv
    #
    vk
    csu
    #
    caddc
    co
    #
    cA
    ce
    cfv
    #
    clt
    wph
    @1
    @6
    wph
    cn0
    cr
    cN
    @0
    wph
    vk
    cF
    cc0
    cn0
    nn0uz
    wph
    0zd
    wph
    @4
    cn0
    wcel
    #
    wa
    #
    @5
    cA
    @4
    cexp
    co
    #
    @4
    cfa
    cfv
    #
    cdiv
    co
    #
    cr
    @9
    @5
    @13
    wceq
    wph
    cA
    vn
    cF
    @4
    effsumlt.1
    eftval
    adantl
    #
    wph
    cA
    cr
    wcel
    @9
    @13
    cr
    wcel
    wph
    cA
    effsumlt.2
    rpred
    #
    cA
    @4
    reeftcl
    sylan
    eqeltrd
    #
    serfre
    effsumlt.3
    ffvelrnd
    wph
    @5
    vk
    cF
    cc0
    @2
    @3
    cn0
    nn0uz
    @3
    eqid
    #
    wph
    cN
    cn0
    wcel
    @2
    cn0
    wcel
    effsumlt.3
    cN
    peano2nn0
    syl
    #
    @10
    @5
    eqidd
    #
    @10
    @5
    @13
    crp
    @14
    @10
    @11
    @12
    wph
    cA
    crp
    wcel
    @4
    cz
    wcel
    @11
    crp
    wcel
    @9
    effsumlt.2
    @4
    nn0z
    cA
    @4
    rpexpcl
    syl2an
    @10
    @12
    @9
    @12
    cn
    wcel
    wph
    @4
    faccl
    adantl
    nnrpd
    rpdivcld
    eqeltrd
    wph
    cA
    cc
    wcel
    #
    @0
    cli
    cdm
    wcel
    wph
    cA
    @15
    recnd
    #
    cA
    vn
    cF
    effsumlt.1
    efcllem
    syl
    #
    isumrpcl
    ltaddrpd
    wph
    @8
    cn0
    @5
    vk
    csu
    #
    cc0
    @2
    c1
    cmin
    co
    #
    cfz
    co
    #
    @5
    vk
    csu
    #
    @6
    caddc
    co
    @7
    wph
    @20
    @8
    @23
    wceq
    @21
    cA
    vk
    vn
    cF
    effsumlt.1
    efval2
    syl
    wph
    @5
    vk
    cF
    cc0
    @2
    @3
    cn0
    nn0uz
    @17
    @18
    @19
    @10
    @5
    @16
    recnd
    #
    @22
    isumsplit
    wph
    @26
    @1
    @6
    caddc
    wph
    @26
    cc0
    cN
    cfz
    co
    #
    @5
    vk
    csu
    @1
    wph
    @25
    @28
    @5
    vk
    wph
    @24
    cN
    cc0
    cfz
    wph
    cN
    cc
    wcel
    c1
    cc
    wcel
    @24
    cN
    wceq
    wph
    cN
    effsumlt.3
    nn0cnd
    ax-1cn
    cN
    c1
    pncan
    sylancl
    oveq2d
    sumeq1d
    wph
    @5
    vk
    cF
    cc0
    cN
    wph
    @4
    @28
    wcel
    #
    wa
    @5
    eqidd
    wph
    cN
    cn0
    cc0
    cuz
    cfv
    effsumlt.3
    nn0uz
    syl6eleq
    @29
    wph
    @9
    @5
    cc
    wcel
    @4
    cN
    elfznn0
    @27
    sylan2
    fsumser
    eqtrd
    oveq1d
    3eqtrd
    breqtrrd
end
