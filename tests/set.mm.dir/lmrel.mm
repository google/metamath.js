include "cv.mm"
include "cuni.mm"
include "cc.mm"
include "cpm.mm"
include "co.mm"
include "wcel.mm"
include "cres.mm"
include "wf.mm"
include "cuz.mm"
include "crn.mm"
include "wrex.mm"
include "wi.mm"
include "wral.mm"
include "w3a.mm"
include "ctop.mm"
include "clm.mm"
include "df-lm.mm"
include "relmptopab.mm"

theorem lmrel
  let cJ: class J
  let vj: setvar j
  let vk: setvar k
  let vf: setvar f
  let vx: setvar x
  let vy: setvar y
  let vg: setvar g
  let vu: setvar u


  assert |- Rel ( ~~>t ` J )

  proof
    vf
    cv
    #
    vj
    cv
    #
    cuni
    #
    cc
    cpm
    co
    wcel
    vx
    cv
    #
    @2
    wcel
    @3
    vu
    cv
    #
    wcel
    vy
    cv
    #
    @4
    @0
    @5
    cres
    wf
    vy
    cuz
    crn
    wrex
    wi
    vu
    @1
    wral
    w3a
    vj
    vf
    vx
    ctop
    cJ
    clm
    vx
    vy
    vu
    vf
    vj
    df-lm
    relmptopab
end
