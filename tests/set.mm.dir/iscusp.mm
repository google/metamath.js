include "cv.mm"
include "cuss.mm"
include "cfv.mm"
include "ccfilu.mm"
include "wcel.mm"
include "ctopn.mm"
include "cflim.mm"
include "co.mm"
include "c0.mm"
include "wne.mm"
include "wi.mm"
include "cbs.mm"
include "cfil.mm"
include "wral.mm"
include "cusp.mm"
include "ccusp.mm"
include "wceq.mm"
include "fveq2.mm"
include "fveq2d.mm"
include "eleq2d.mm"
include "oveq1d.mm"
include "neeq1d.mm"
include "imbi12d.mm"
include "raleqbidv.mm"
include "df-cusp.mm"
include "elrab2.mm"

theorem iscusp
  let cW: class W
  let vc: setvar c
  let vw: setvar w

  disjoint W c
  disjoint c w
  disjoint W w
  assert |- ( W e. CUnifSp <-> ( W e. UnifSp /\ A. c e. ( Fil ` ( Base ` W ) ) ( c e. ( CauFilU ` ( UnifSt ` W ) ) -> ( ( TopOpen ` W ) fLim c ) =/= (/) ) ) )

  proof
    vc
    cv
    #
    vw
    cv
    #
    cuss
    cfv
    #
    ccfilu
    cfv
    #
    wcel
    #
    @1
    ctopn
    cfv
    #
    @0
    cflim
    co
    #
    c0
    wne
    #
    wi
    #
    vc
    @1
    cbs
    cfv
    #
    cfil
    cfv
    #
    wral
    @0
    cW
    cuss
    cfv
    #
    ccfilu
    cfv
    #
    wcel
    #
    cW
    ctopn
    cfv
    #
    @0
    cflim
    co
    #
    c0
    wne
    #
    wi
    #
    vc
    cW
    cbs
    cfv
    #
    cfil
    cfv
    #
    wral
    vw
    cW
    cusp
    ccusp
    @1
    cW
    wceq
    #
    @8
    @17
    vc
    @10
    @19
    @20
    @9
    @18
    cfil
    @1
    cW
    cbs
    fveq2
    fveq2d
    @20
    @4
    @13
    @7
    @16
    @20
    @3
    @12
    @0
    @20
    @2
    @11
    ccfilu
    @1
    cW
    cuss
    fveq2
    fveq2d
    eleq2d
    @20
    @6
    @15
    c0
    @20
    @5
    @14
    @0
    cflim
    @1
    cW
    ctopn
    fveq2
    oveq1d
    neeq1d
    imbi12d
    raleqbidv
    vw
    vc
    df-cusp
    elrab2
end
