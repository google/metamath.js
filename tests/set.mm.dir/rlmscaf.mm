include "cmgp.mm"
include "cfv.mm"
include "cplusf.mm"
include "cbs.mm"
include "cv.mm"
include "cmulr.mm"
include "co.mm"
include "cmpt2.mm"
include "crglmod.mm"
include "cscaf.mm"
include "eqid.mm"
include "mgpbas.mm"
include "mgpplusg.mm"
include "plusffval.mm"
include "cid.mm"
include "rlmbas.mm"
include "rlmsca2.mm"
include "c1.mm"
include "df-base.mm"
include "strfvi.mm"
include "rlmvsca.mm"
include "scaffval.mm"
include "eqtr4i.mm"

theorem rlmscaf
  let cR: class R
  let vx: setvar x
  let vy: setvar y


  assert |- ( +f ` ( mulGrp ` R ) ) = ( .sf ` ( ringLMod ` R ) )

  proof
    cR
    cmgp
    cfv
    #
    cplusf
    cfv
    #
    vx
    vy
    cR
    cbs
    cfv
    #
    @2
    vx
    cv
    vy
    cv
    cR
    cmulr
    cfv
    #
    co
    cmpt2
    cR
    crglmod
    cfv
    #
    cscaf
    cfv
    #
    vx
    vy
    @2
    @3
    @1
    @0
    @2
    cR
    @0
    @0
    eqid
    #
    @2
    eqid
    #
    mgpbas
    cR
    @3
    @0
    @6
    @3
    eqid
    mgpplusg
    @1
    eqid
    plusffval
    vx
    vy
    @2
    @5
    @3
    cR
    cid
    cfv
    @2
    @4
    cR
    rlmbas
    cR
    rlmsca2
    cR
    cbs
    c1
    @2
    df-base
    @7
    strfvi
    @5
    eqid
    cR
    rlmvsca
    scaffval
    eqtr4i
end
