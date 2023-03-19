include "cq.mm"
include "cz.mm"
include "cn.mm"
include "cv.mm"
include "cdiv.mm"
include "co.mm"
include "cmpt2.mm"
include "crn.mm"
include "cvv.mm"
include "wcel.mm"
include "wceq.mm"
include "wrex.mm"
include "elq.mm"
include "eqid.mm"
include "ovex.mm"
include "elrnmpt2.mm"
include "bitr4i.mm"
include "eqriv.mm"
include "zexALT.mm"
include "nnexALT.mm"
include "mpt2ex.mm"
include "rnex.mm"
include "eqeltri.mm"

theorem qexALT
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- QQ e. _V

  proof
    cq
    vy
    vz
    cz
    cn
    vy
    cv
    #
    vz
    cv
    #
    cdiv
    co
    #
    cmpt2
    #
    crn
    #
    cvv
    vx
    cq
    @4
    vx
    cv
    #
    cq
    wcel
    @5
    @2
    wceq
    vz
    cn
    wrex
    vy
    cz
    wrex
    @5
    @4
    wcel
    vy
    vz
    @5
    elq
    vy
    vz
    cz
    cn
    @2
    @5
    @3
    @3
    eqid
    @0
    @1
    cdiv
    ovex
    elrnmpt2
    bitr4i
    eqriv
    @3
    vy
    vz
    cz
    cn
    @2
    zexALT
    nnexALT
    mpt2ex
    rnex
    eqeltri
end
