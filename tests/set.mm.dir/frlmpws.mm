include "wcel.mm"
include "wa.mm"
include "crglmod.mm"
include "cfv.mm"
include "csn.mm"
include "cxp.mm"
include "cdsmm.mm"
include "co.mm"
include "csca.mm"
include "cprds.mm"
include "cress.mm"
include "cpws.mm"
include "cbs.mm"
include "eqid.mm"
include "dsmmval2.mm"
include "wceq.mm"
include "rlmsca.mm"
include "adantr.mm"
include "oveq1d.mm"
include "frlmval.mm"
include "eqcomd.mm"
include "fveq2d.mm"
include "syl6eqr.mm"
include "oveq12d.mm"
include "syl5eq.mm"
include "cvv.mm"
include "fvex.mm"
include "pwsval.mm"
include "mpan.mm"
include "adantl.mm"
include "3eqtr4d.mm"

theorem frlmpws
  let cB: class B
  let cR: class R
  let cF: class F
  let cI: class I
  let cV: class V
  let cW: class W
  let vr: setvar r
  let vi: setvar i
  assume frlmval.f: |- F = ( R freeLMod I )
  assume frlmpws.b: |- B = ( Base ` F )


  assert |- ( ( R e. V /\ I e. W ) -> F = ( ( ( ringLMod ` R ) ^s I ) |`s B ) )

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
    cI
    cR
    crglmod
    cfv
    #
    csn
    cxp
    #
    cdsmm
    co
    #
    @3
    csca
    cfv
    #
    @4
    cprds
    co
    #
    cB
    cress
    co
    #
    cF
    @3
    cI
    cpws
    co
    #
    cB
    cress
    co
    @2
    @5
    cR
    @4
    cprds
    co
    #
    @5
    cbs
    cfv
    #
    cress
    co
    @8
    @11
    @4
    cR
    @11
    eqid
    dsmmval2
    @2
    @10
    @7
    @11
    cB
    cress
    @2
    cR
    @6
    @4
    cprds
    @0
    cR
    @6
    wceq
    @1
    cR
    cV
    rlmsca
    adantr
    oveq1d
    @2
    @11
    cF
    cbs
    cfv
    cB
    @2
    @5
    cF
    cbs
    @2
    cF
    @5
    cR
    cF
    cI
    cV
    cW
    frlmval.f
    frlmval
    #
    eqcomd
    fveq2d
    frlmpws.b
    syl6eqr
    oveq12d
    syl5eq
    @12
    @2
    @9
    @7
    cB
    cress
    @1
    @9
    @7
    wceq
    #
    @0
    @3
    cvv
    wcel
    @1
    @13
    cR
    crglmod
    fvex
    @3
    @6
    cI
    cvv
    cW
    @9
    @9
    eqid
    @6
    eqid
    pwsval
    mpan
    adantl
    oveq1d
    3eqtr4d
end
