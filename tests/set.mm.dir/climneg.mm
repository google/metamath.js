include "cv.mm"
include "cfv.mm"
include "cneg.mm"
include "cmpt.mm"
include "c1.mm"
include "cmul.mm"
include "co.mm"
include "cli.mm"
include "cvv.mm"
include "nfmpt1.mm"
include "wcel.mm"
include "cuz.mm"
include "fvex.mm"
include "eqeltri.mm"
include "mptex.mm"
include "a1i.mm"
include "1cnd.mm"
include "negcld.mm"
include "wceq.mm"
include "cc.mm"
include "eqidd.mm"
include "wa.mm"
include "id.mm"
include "fvmptd.mm"
include "adantl.mm"
include "climconst.mm"
include "neg1cn.mm"
include "eqid.mm"
include "fvmpt2.mm"
include "mpan2.mm"
include "syl6eqel.mm"
include "simpr.mm"
include "syl2anc.mm"
include "mulm1d.mm"
include "eqcomd.mm"
include "oveq1d.mm"
include "3eqtr2d.mm"
include "climmulf.mm"
include "wbr.mm"
include "climcl.mm"
include "syl.mm"
include "breqtrd.mm"

theorem climneg
  let wph: wff ph
  let cA: class A
  let vk: setvar k
  let cF: class F
  let cM: class M
  let cZ: class Z
  let vj: setvar j
  assume climneg.1: |- F/ k ph
  assume climneg.2: |- F/_ k F
  assume climneg.3: |- Z = ( ZZ>= ` M )
  assume climneg.4: |- ( ph -> M e. ZZ )
  assume climneg.5: |- ( ph -> F ~~> A )
  assume climneg.6: |- ( ( ph /\ k e. Z ) -> ( F ` k ) e. CC )

  disjoint Z k
  disjoint j k
  disjoint j ph
  disjoint Z j
  assert |- ( ph -> ( k e. Z |-> -u ( F ` k ) ) ~~> -u A )

  proof
    wph
    vk
    cZ
    vk
    cv
    #
    cF
    cfv
    #
    cneg
    #
    cmpt
    #
    c1
    cneg
    #
    cA
    cmul
    co
    cA
    cneg
    cli
    wph
    @4
    cA
    vk
    vk
    cZ
    @4
    cmpt
    #
    cF
    @3
    cM
    cvv
    cZ
    climneg.1
    vk
    cZ
    @4
    nfmpt1
    climneg.2
    vk
    cZ
    @2
    nfmpt1
    climneg.3
    climneg.4
    wph
    @4
    vj
    @5
    cM
    cvv
    cZ
    climneg.3
    climneg.4
    @5
    cvv
    wcel
    wph
    vk
    cZ
    @4
    cZ
    cM
    cuz
    cfv
    cvv
    climneg.3
    cM
    cuz
    fvex
    eqeltri
    #
    mptex
    a1i
    wph
    c1
    wph
    1cnd
    negcld
    vj
    cv
    #
    cZ
    wcel
    #
    @7
    @5
    cfv
    @4
    wceq
    wph
    @8
    vk
    @7
    @4
    @4
    cZ
    @5
    cc
    @8
    @5
    eqidd
    @8
    @0
    @7
    wceq
    wa
    @4
    eqidd
    @8
    id
    @8
    c1
    @8
    1cnd
    negcld
    fvmptd
    adantl
    climconst
    @3
    cvv
    wcel
    wph
    vk
    cZ
    @2
    @6
    mptex
    a1i
    climneg.5
    @0
    cZ
    wcel
    #
    @0
    @5
    cfv
    #
    cc
    wcel
    wph
    @9
    @10
    @4
    cc
    @9
    @4
    cc
    wcel
    @10
    @4
    wceq
    neg1cn
    vk
    cZ
    @4
    cc
    @5
    @5
    eqid
    fvmpt2
    mpan2
    #
    neg1cn
    syl6eqel
    adantl
    climneg.6
    wph
    @9
    wa
    #
    @0
    @3
    cfv
    #
    @2
    @4
    @1
    cmul
    co
    @10
    @1
    cmul
    co
    @12
    @9
    @2
    cc
    wcel
    @13
    @2
    wceq
    wph
    @9
    simpr
    @12
    @1
    climneg.6
    negcld
    vk
    cZ
    @2
    cc
    @3
    @3
    eqid
    fvmpt2
    syl2anc
    @12
    @1
    climneg.6
    mulm1d
    @12
    @4
    @10
    @1
    cmul
    @9
    @4
    @10
    wceq
    wph
    @9
    @10
    @4
    @11
    eqcomd
    adantl
    oveq1d
    3eqtr2d
    climmulf
    wph
    cA
    wph
    cF
    cA
    cli
    wbr
    cA
    cc
    wcel
    climneg.5
    cA
    cF
    climcl
    syl
    mulm1d
    breqtrd
end
