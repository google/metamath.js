include "crng.mm"
include "wcel.mm"
include "wa.mm"
include "crngh.mm"
include "co.mm"
include "cghm.mm"
include "cmgp.mm"
include "cfv.mm"
include "cmgmhm.mm"
include "cin.mm"
include "cv.mm"
include "eqid.mm"
include "isrnghmmul.mm"
include "elin.mm"
include "ibar.mm"
include "syl5rbb.mm"
include "syl5bb.mm"
include "eqrdv.mm"

theorem rnghmval2
  let cR: class R
  let cS: class S
  let vh: setvar h
  let vk: setvar k
  let vx: setvar x


  assert |- ( ( R e. Rng /\ S e. Rng ) -> ( R RngHomo S ) = ( ( R GrpHom S ) i^i ( ( mulGrp ` R ) MgmHom ( mulGrp ` S ) ) ) )

  proof
    cR
    crng
    wcel
    cS
    crng
    wcel
    wa
    #
    vh
    cR
    cS
    crngh
    co
    #
    cR
    cS
    cghm
    co
    #
    cR
    cmgp
    cfv
    #
    cS
    cmgp
    cfv
    #
    cmgmhm
    co
    #
    cin
    #
    vh
    cv
    #
    @1
    wcel
    @0
    @7
    @2
    wcel
    @7
    @5
    wcel
    wa
    #
    wa
    #
    @0
    @7
    @6
    wcel
    #
    cR
    cS
    @7
    @3
    @4
    @3
    eqid
    @4
    eqid
    isrnghmmul
    @10
    @8
    @0
    @9
    @7
    @2
    @5
    elin
    @0
    @8
    ibar
    syl5rbb
    syl5bb
    eqrdv
end
