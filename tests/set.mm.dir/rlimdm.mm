include "crli.mm"
include "cdm.mm"
include "wcel.mm"
include "cfv.mm"
include "wbr.mm"
include "cv.mm"
include "wex.mm"
include "eldmg.mm"
include "ibi.mm"
include "wa.mm"
include "simpr.mm"
include "cio.mm"
include "df-fv.mm"
include "cvv.mm"
include "wceq.mm"
include "vex.mm"
include "wb.mm"
include "cc.mm"
include "wf.mm"
include "adantr.mm"
include "cxr.mm"
include "clt.mm"
include "csup.mm"
include "cpnf.mm"
include "simprr.mm"
include "simprl.mm"
include "rlimuni.mm"
include "expr.mm"
include "breq2.mm"
include "syl5ibrcom.mm"
include "impbid.mm"
include "iota5.mm"
include "mpan2.mm"
include "syl5eq.mm"
include "breqtrrd.mm"
include "ex.mm"
include "exlimdv.mm"
include "syl5.mm"
include "rlimrel.mm"
include "releldmi.mm"
include "impbid1.mm"

theorem rlimdm
  let wph: wff ph
  let cA: class A
  let cF: class F
  let vj: setvar j
  let vk: setvar k
  let cB: class B
  let cC: class C
  let vx: setvar x
  let vy: setvar y
  assume rlimuni.1: |- ( ph -> F : A --> CC )
  assume rlimuni.2: |- ( ph -> sup ( A , RR* , < ) = +oo )


  assert |- ( ph -> ( F e. dom ~~>r <-> F ~~>r ( ~~>r ` F ) ) )

  proof
    wph
    cF
    crli
    cdm
    #
    wcel
    #
    cF
    cF
    crli
    cfv
    #
    crli
    wbr
    #
    @1
    cF
    vx
    cv
    #
    crli
    wbr
    #
    vx
    wex
    #
    wph
    @3
    @1
    @6
    vx
    cF
    crli
    @0
    eldmg
    ibi
    wph
    @5
    @3
    vx
    wph
    @5
    @3
    wph
    @5
    wa
    #
    cF
    @4
    @2
    crli
    wph
    @5
    simpr
    #
    @7
    @2
    cF
    vy
    cv
    #
    crli
    wbr
    #
    vy
    cio
    #
    @4
    vy
    cF
    crli
    df-fv
    @7
    @4
    cvv
    wcel
    #
    @11
    @4
    wceq
    vx
    vex
    @7
    @10
    vy
    @4
    cvv
    @7
    @10
    @9
    @4
    wceq
    #
    wb
    @12
    @7
    @10
    @13
    wph
    @5
    @10
    @13
    wph
    @5
    @10
    wa
    #
    wa
    cA
    @9
    @4
    cF
    wph
    cA
    cc
    cF
    wf
    @14
    rlimuni.1
    adantr
    wph
    cA
    cxr
    clt
    csup
    cpnf
    wceq
    @14
    rlimuni.2
    adantr
    wph
    @5
    @10
    simprr
    wph
    @5
    @10
    simprl
    rlimuni
    expr
    @7
    @10
    @13
    @5
    @8
    @9
    @4
    cF
    crli
    breq2
    syl5ibrcom
    impbid
    adantr
    iota5
    mpan2
    syl5eq
    breqtrrd
    ex
    exlimdv
    syl5
    cF
    @2
    crli
    rlimrel
    releldmi
    impbid1
end
