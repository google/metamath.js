include "wcel.mm"
include "wa.mm"
include "crglmod.mm"
include "cfv.mm"
include "csca.mm"
include "cpws.mm"
include "co.mm"
include "cbs.mm"
include "cress.mm"
include "wceq.mm"
include "cvv.mm"
include "fvex.mm"
include "eqid.mm"
include "pwssca.mm"
include "mpan.mm"
include "adantl.mm"
include "resssca.mm"
include "ax-mp.mm"
include "syl6eq.mm"
include "rlmsca.mm"
include "adantr.mm"
include "frlmpws.mm"
include "fveq2d.mm"
include "3eqtr4d.mm"

theorem frlmsca
  let cR: class R
  let cF: class F
  let cI: class I
  let cV: class V
  let cW: class W
  let vr: setvar r
  let vi: setvar i
  assume frlmval.f: |- F = ( R freeLMod I )


  assert |- ( ( R e. V /\ I e. W ) -> R = ( Scalar ` F ) )

  proof
    cR
    cV
    wcel
    #
    cI
    cW
    wcel
    #
    wa
    #
    cR
    crglmod
    cfv
    #
    csca
    cfv
    #
    @3
    cI
    cpws
    co
    #
    cF
    cbs
    cfv
    #
    cress
    co
    #
    csca
    cfv
    #
    cR
    cF
    csca
    cfv
    @2
    @4
    @5
    csca
    cfv
    #
    @8
    @1
    @4
    @9
    wceq
    #
    @0
    @3
    cvv
    wcel
    @1
    @10
    cR
    crglmod
    fvex
    @3
    @4
    cI
    cvv
    cW
    @5
    @5
    eqid
    @4
    eqid
    pwssca
    mpan
    adantl
    @6
    cvv
    wcel
    @9
    @8
    wceq
    cF
    cbs
    fvex
    @6
    @9
    @5
    @7
    cvv
    @7
    eqid
    @9
    eqid
    resssca
    ax-mp
    syl6eq
    @0
    cR
    @4
    wceq
    @1
    cR
    cV
    rlmsca
    adantr
    @2
    cF
    @7
    csca
    @6
    cR
    cF
    cI
    cV
    cW
    frlmval.f
    @6
    eqid
    frlmpws
    fveq2d
    3eqtr4d
end
