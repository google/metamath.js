include "crg.mm"
include "wcel.mm"
include "wa.mm"
include "crglmod.mm"
include "cfv.mm"
include "csn.mm"
include "cxp.mm"
include "cdsmm.mm"
include "co.mm"
include "cbs.mm"
include "frlmval.mm"
include "fveq2d.mm"
include "syl5eq.mm"
include "cprds.mm"
include "clss.mm"
include "simpr.mm"
include "simpl.mm"
include "clmod.mm"
include "wf.mm"
include "rlmlmod.mm"
include "adantr.mm"
include "fconst6g.mm"
include "syl.mm"
include "cv.mm"
include "csca.mm"
include "wceq.mm"
include "fvex.mm"
include "fvconst2.mm"
include "adantl.mm"
include "rlmsca.mm"
include "ad2antrr.mm"
include "eqtr4d.mm"
include "eqid.mm"
include "dsmmlss.mm"
include "cpws.mm"
include "cvv.mm"
include "pwsval.mm"
include "mpan.mm"
include "eqcomd.mm"
include "oveq1d.mm"
include "eqtr2d.mm"
include "syl6eqr.mm"
include "eleqtrd.mm"
include "eqeltrd.mm"

theorem frlmlss
  let cB: class B
  let cR: class R
  let cU: class U
  let cF: class F
  let cI: class I
  let cW: class W
  let vr: setvar r
  let vi: setvar i
  assume frlmval.f: |- F = ( R freeLMod I )
  assume frlmpws.b: |- B = ( Base ` F )
  assume frlmlss.u: |- U = ( LSubSp ` ( ( ringLMod ` R ) ^s I ) )


  assert |- ( ( R e. Ring /\ I e. W ) -> B e. U )

  proof
    cR
    crg
    wcel
    #
    cI
    cW
    wcel
    #
    wa
    #
    cB
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
    cbs
    cfv
    #
    cU
    @2
    cB
    cF
    cbs
    cfv
    @6
    frlmpws.b
    @2
    cF
    @5
    cbs
    cR
    cF
    cI
    crg
    cW
    frlmval.f
    frlmval
    fveq2d
    syl5eq
    @2
    @6
    cR
    @4
    cprds
    co
    #
    clss
    cfv
    #
    cU
    @2
    vi
    @7
    @4
    cR
    @8
    @6
    cI
    cW
    @0
    @1
    simpr
    @0
    @1
    simpl
    @2
    @3
    clmod
    wcel
    #
    cI
    clmod
    @4
    wf
    @0
    @9
    @1
    cR
    rlmlmod
    adantr
    cI
    @3
    clmod
    fconst6g
    syl
    @2
    vi
    cv
    #
    cI
    wcel
    #
    wa
    #
    @10
    @4
    cfv
    #
    csca
    cfv
    @3
    csca
    cfv
    #
    cR
    @12
    @13
    @3
    csca
    @11
    @13
    @3
    wceq
    @2
    cI
    @3
    @10
    cR
    crglmod
    fvex
    #
    fvconst2
    adantl
    fveq2d
    @0
    cR
    @14
    wceq
    @1
    @11
    cR
    crg
    rlmsca
    #
    ad2antrr
    eqtr4d
    @7
    eqid
    @8
    eqid
    @6
    eqid
    dsmmlss
    @2
    @8
    @3
    cI
    cpws
    co
    #
    clss
    cfv
    cU
    @2
    @7
    @17
    clss
    @2
    @17
    @14
    @4
    cprds
    co
    #
    @7
    @1
    @17
    @18
    wceq
    #
    @0
    @3
    cvv
    wcel
    @1
    @19
    @15
    @3
    @14
    cI
    cvv
    cW
    @17
    @17
    eqid
    @14
    eqid
    pwsval
    mpan
    adantl
    @2
    @14
    cR
    @4
    cprds
    @0
    @14
    cR
    wceq
    @1
    @0
    cR
    @14
    @16
    eqcomd
    adantr
    oveq1d
    eqtr2d
    fveq2d
    frlmlss.u
    syl6eqr
    eleqtrd
    eqeltrd
end
