include "wcel.mm"
include "cfn.mm"
include "wa.mm"
include "crglmod.mm"
include "cfv.mm"
include "csn.mm"
include "cxp.mm"
include "cdsmm.mm"
include "co.mm"
include "csca.mm"
include "cprds.mm"
include "cpws.mm"
include "wceq.mm"
include "wfn.mm"
include "cvv.mm"
include "fvex.mm"
include "fnconstg.mm"
include "ax-mp.mm"
include "dsmmfi.mm"
include "mpan.mm"
include "adantl.mm"
include "rlmsca.mm"
include "adantr.mm"
include "oveq1d.mm"
include "eqtrd.mm"
include "frlmval.mm"
include "eqid.mm"
include "pwsval.mm"
include "3eqtr4d.mm"

theorem frlmpwsfi
  let cR: class R
  let cF: class F
  let cI: class I
  let cV: class V
  let vr: setvar r
  let vi: setvar i
  let cW: class W
  assume frlmval.f: |- F = ( R freeLMod I )


  assert |- ( ( R e. V /\ I e. Fin ) -> F = ( ( ringLMod ` R ) ^s I ) )

  proof
    cR
    cV
    wcel
    #
    cI
    cfn
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
    cF
    @3
    cI
    cpws
    co
    #
    @2
    @5
    cR
    @4
    cprds
    co
    #
    @7
    @1
    @5
    @9
    wceq
    #
    @0
    @4
    cI
    wfn
    #
    @1
    @10
    @3
    cvv
    wcel
    #
    @11
    cR
    crglmod
    fvex
    #
    cI
    @3
    cvv
    fnconstg
    ax-mp
    @4
    cR
    cI
    dsmmfi
    mpan
    adantl
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
    eqtrd
    cR
    cF
    cI
    cV
    cfn
    frlmval.f
    frlmval
    @1
    @8
    @7
    wceq
    #
    @0
    @12
    @1
    @14
    @13
    @3
    @6
    cI
    cvv
    cfn
    @8
    @8
    eqid
    @6
    eqid
    pwsval
    mpan
    adantl
    3eqtr4d
end
