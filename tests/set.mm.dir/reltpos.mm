include "ctpos.mm"
include "cdm.mm"
include "ccnv.mm"
include "c0.mm"
include "csn.mm"
include "cun.mm"
include "crn.mm"
include "cxp.mm"
include "wss.mm"
include "wrel.mm"
include "tposssxp.mm"
include "relxp.mm"
include "relss.mm"
include "mp2.mm"

theorem reltpos
  let cF: class F
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let vw: setvar w
  let vz: setvar z
  let cG: class G


  assert |- Rel tpos F

  proof
    cF
    ctpos
    #
    cF
    cdm
    ccnv
    c0
    csn
    cun
    #
    cF
    crn
    #
    cxp
    #
    wss
    @3
    wrel
    @0
    wrel
    cF
    tposssxp
    @1
    @2
    relxp
    @0
    @3
    relss
    mp2
end
