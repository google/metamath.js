include "ccusp.mm"
include "wcel.mm"
include "cusp.mm"
include "cv.mm"
include "cuss.mm"
include "cfv.mm"
include "ccfilu.mm"
include "ctopn.mm"
include "cflim.mm"
include "co.mm"
include "c0.mm"
include "wne.mm"
include "wi.mm"
include "cbs.mm"
include "cfil.mm"
include "wral.mm"
include "wa.mm"
include "iscusp.mm"
include "fveq2i.mm"
include "eleq2i.mm"
include "oveq1i.mm"
include "neeq1i.mm"
include "imbi12i.mm"
include "raleqbii.mm"
include "anbi2i.mm"
include "bitr4i.mm"

theorem iscusp2
  let cB: class B
  let cU: class U
  let cJ: class J
  let cW: class W
  let vc: setvar c
  assume iscusp2.1: |- B = ( Base ` W )
  assume iscusp2.2: |- U = ( UnifSt ` W )
  assume iscusp2.3: |- J = ( TopOpen ` W )

  disjoint W c
  assert |- ( W e. CUnifSp <-> ( W e. UnifSp /\ A. c e. ( Fil ` B ) ( c e. ( CauFilU ` U ) -> ( J fLim c ) =/= (/) ) ) )

  proof
    cW
    ccusp
    wcel
    cW
    cusp
    wcel
    #
    vc
    cv
    #
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
    @1
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
    #
    wa
    @0
    @1
    cU
    ccfilu
    cfv
    #
    wcel
    #
    cJ
    @1
    cflim
    co
    #
    c0
    wne
    #
    wi
    #
    vc
    cB
    cfil
    cfv
    #
    wral
    #
    wa
    cW
    vc
    iscusp
    @18
    @11
    @0
    @16
    @8
    vc
    @17
    @10
    cB
    @9
    cfil
    iscusp2.1
    fveq2i
    @13
    @4
    @15
    @7
    @12
    @3
    @1
    cU
    @2
    ccfilu
    iscusp2.2
    fveq2i
    eleq2i
    @14
    @6
    c0
    cJ
    @5
    @1
    cflim
    iscusp2.3
    oveq1i
    neeq1i
    imbi12i
    raleqbii
    anbi2i
    bitr4i
end
