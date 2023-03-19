include "wcel.mm"
include "wa.mm"
include "cvv.mm"
include "cdm.mm"
include "cv.mm"
include "cfv.mm"
include "co.mm"
include "cmpt.mm"
include "cofc.mm"
include "wceq.mm"
include "elex.mm"
include "adantr.mm"
include "adantl.mm"
include "dmexg.mm"
include "mptexg.mm"
include "syl.mm"
include "simpl.mm"
include "dmeqd.mm"
include "fveq1d.mm"
include "simpr.mm"
include "oveq12d.mm"
include "mpteq12dv.mm"
include "df-ofc.mm"
include "ovmpt2ga.mm"
include "syl3anc.mm"

theorem ofcfval3
  let vx: setvar x
  let cC: class C
  let cR: class R
  let cF: class F
  let cV: class V
  let cW: class W
  let vc: setvar c
  let vf: setvar f

  disjoint C x
  disjoint F x
  disjoint R x
  disjoint c f
  disjoint c x
  disjoint C c
  disjoint f x
  disjoint C f
  disjoint F c
  disjoint F f
  disjoint R c
  disjoint R f
  assert |- ( ( F e. V /\ C e. W ) -> ( F oFC R C ) = ( x e. dom F |-> ( ( F ` x ) R C ) ) )

  proof
    cF
    cV
    wcel
    #
    cC
    cW
    wcel
    #
    wa
    cF
    cvv
    wcel
    #
    cC
    cvv
    wcel
    #
    vx
    cF
    cdm
    #
    vx
    cv
    #
    cF
    cfv
    #
    cC
    cR
    co
    #
    cmpt
    #
    cvv
    wcel
    #
    cF
    cC
    cR
    cofc
    #
    co
    @8
    wceq
    @0
    @2
    @1
    cF
    cV
    elex
    adantr
    @1
    @3
    @0
    cC
    cW
    elex
    adantl
    @0
    @9
    @1
    @0
    @4
    cvv
    wcel
    @9
    cF
    cV
    dmexg
    vx
    @4
    @7
    cvv
    mptexg
    syl
    adantr
    vf
    vc
    cF
    cC
    cvv
    cvv
    vx
    vf
    cv
    #
    cdm
    #
    @5
    @11
    cfv
    #
    vc
    cv
    #
    cR
    co
    #
    cmpt
    @8
    @10
    cvv
    @11
    cF
    wceq
    #
    @14
    cC
    wceq
    #
    wa
    #
    vx
    @12
    @15
    @4
    @7
    @18
    @11
    cF
    @16
    @17
    simpl
    #
    dmeqd
    @18
    @13
    @6
    @14
    cC
    cR
    @18
    @5
    @11
    cF
    @19
    fveq1d
    @16
    @17
    simpr
    oveq12d
    mpteq12dv
    vx
    cR
    vf
    vc
    df-ofc
    ovmpt2ga
    syl3anc
end
