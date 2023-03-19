include "ce.mm"
include "cfv.mm"
include "cuz.mm"
include "cv.mm"
include "csu.mm"
include "caddc.mm"
include "co.mm"
include "cexp.mm"
include "cfa.mm"
include "cdiv.mm"
include "c1.mm"
include "eqid.mm"
include "cz.mm"
include "wcel.mm"
include "nn0zi.mm"
include "a1i.mm"
include "wa.mm"
include "eqidd.mm"
include "cn0.mm"
include "cc.mm"
include "eluznn0.mm"
include "mpan.mm"
include "wceq.mm"
include "eftval.mm"
include "adantl.mm"
include "eftcl.mm"
include "sylan.mm"
include "eqeltrd.mm"
include "sylan2.mm"
include "cseq.mm"
include "cli.mm"
include "cdm.mm"
include "eftlcvg.mm"
include "sylancl.mm"
include "isum1p.mm"
include "ax-mp.mm"
include "eqcomi.mm"
include "fveq2i.mm"
include "sumeq1i.mm"
include "oveq12i.mm"
include "syl6eq.mm"
include "oveq2d.mm"
include "peano2nn0.mm"
include "eqeltri.mm"
include "eftlcl.mm"
include "addassd.mm"
include "eqtr4d.mm"
include "oveq1d.mm"
include "3eqtrd.mm"

theorem efsep
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cD: class D
  let vk: setvar k
  let vn: setvar n
  let cF: class F
  let cM: class M
  let cN: class N
  assume efsep.1: |- F = ( n e. NN0 |-> ( ( A ^ n ) / ( ! ` n ) ) )
  assume efsep.2: |- N = ( M + 1 )
  assume efsep.3: |- M e. NN0
  assume efsep.4: |- ( ph -> A e. CC )
  assume efsep.5: |- ( ph -> B e. CC )
  assume efsep.6: |- ( ph -> ( exp ` A ) = ( B + sum_ k e. ( ZZ>= ` M ) ( F ` k ) ) )
  assume efsep.7: |- ( ph -> ( B + ( ( A ^ M ) / ( ! ` M ) ) ) = D )

  disjoint k n
  disjoint A k
  disjoint A n
  disjoint F k
  disjoint M k
  disjoint M n
  disjoint N k
  disjoint N n
  disjoint k ph
  assert |- ( ph -> ( exp ` A ) = ( D + sum_ k e. ( ZZ>= ` N ) ( F ` k ) ) )

  proof
    wph
    cA
    ce
    cfv
    cB
    cM
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
    cB
    cA
    cM
    cexp
    co
    cM
    cfa
    cfv
    cdiv
    co
    #
    caddc
    co
    #
    cN
    cuz
    cfv
    #
    @2
    vk
    csu
    #
    caddc
    co
    #
    cD
    @8
    caddc
    co
    efsep.6
    wph
    @4
    cB
    @5
    @8
    caddc
    co
    #
    caddc
    co
    @9
    wph
    @3
    @10
    cB
    caddc
    wph
    @3
    cM
    cF
    cfv
    #
    cM
    c1
    caddc
    co
    #
    cuz
    cfv
    #
    @2
    vk
    csu
    #
    caddc
    co
    @10
    wph
    @2
    vk
    cF
    cM
    @0
    @0
    eqid
    cM
    cz
    wcel
    wph
    cM
    efsep.3
    nn0zi
    a1i
    wph
    @1
    @0
    wcel
    #
    wa
    @2
    eqidd
    @15
    wph
    @1
    cn0
    wcel
    #
    @2
    cc
    wcel
    cM
    cn0
    wcel
    #
    @15
    @16
    efsep.3
    @1
    cM
    eluznn0
    mpan
    wph
    @16
    wa
    @2
    cA
    @1
    cexp
    co
    @1
    cfa
    cfv
    cdiv
    co
    #
    cc
    @16
    @2
    @18
    wceq
    wph
    cA
    vn
    cF
    @1
    efsep.1
    eftval
    adantl
    wph
    cA
    cc
    wcel
    #
    @16
    @18
    cc
    wcel
    efsep.4
    cA
    @1
    eftcl
    sylan
    eqeltrd
    sylan2
    wph
    @19
    @17
    caddc
    cF
    cM
    cseq
    cli
    cdm
    wcel
    efsep.4
    efsep.3
    cA
    vn
    cF
    cM
    efsep.1
    eftlcvg
    sylancl
    isum1p
    @11
    @5
    @14
    @8
    caddc
    @17
    @11
    @5
    wceq
    efsep.3
    cA
    vn
    cF
    cM
    efsep.1
    eftval
    ax-mp
    @13
    @7
    @2
    vk
    @12
    cN
    cuz
    cN
    @12
    efsep.2
    eqcomi
    fveq2i
    sumeq1i
    oveq12i
    syl6eq
    oveq2d
    wph
    cB
    @5
    @8
    efsep.5
    wph
    @19
    @17
    @5
    cc
    wcel
    efsep.4
    efsep.3
    cA
    cM
    eftcl
    sylancl
    wph
    @19
    cN
    cn0
    wcel
    @8
    cc
    wcel
    efsep.4
    cN
    @12
    cn0
    efsep.2
    @17
    @12
    cn0
    wcel
    efsep.3
    cM
    peano2nn0
    ax-mp
    eqeltri
    cA
    vk
    vn
    cF
    cN
    efsep.1
    eftlcl
    sylancl
    addassd
    eqtr4d
    wph
    @6
    cD
    @8
    caddc
    efsep.7
    oveq1d
    3eqtrd
end
