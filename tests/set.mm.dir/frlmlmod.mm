include "crg.mm"
include "wcel.mm"
include "wa.mm"
include "crglmod.mm"
include "cfv.mm"
include "csn.mm"
include "cxp.mm"
include "cdsmm.mm"
include "co.mm"
include "clmod.mm"
include "frlmval.mm"
include "simpr.mm"
include "simpl.mm"
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
include "fveq2d.mm"
include "rlmsca.mm"
include "ad2antrr.mm"
include "eqtr4d.mm"
include "eqid.mm"
include "dsmmlmod.mm"
include "eqeltrd.mm"

theorem frlmlmod
  let cR: class R
  let cF: class F
  let cI: class I
  let cW: class W
  let vr: setvar r
  let vi: setvar i
  assume frlmval.f: |- F = ( R freeLMod I )


  assert |- ( ( R e. Ring /\ I e. W ) -> F e. LMod )

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
    cF
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
    clmod
    cR
    cF
    cI
    crg
    cW
    frlmval.f
    frlmval
    @2
    vi
    @5
    @4
    cR
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
    @6
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
    @7
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
    @9
    @10
    @3
    csca
    @8
    @10
    @3
    wceq
    @2
    cI
    @3
    @7
    cR
    crglmod
    fvex
    fvconst2
    adantl
    fveq2d
    @0
    cR
    @11
    wceq
    @1
    @8
    cR
    crg
    rlmsca
    ad2antrr
    eqtr4d
    @5
    eqid
    dsmmlmod
    eqeltrd
end
