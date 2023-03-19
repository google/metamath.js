include "cv.mm"
include "cbs.mm"
include "cfv.mm"
include "cpw.mm"
include "wcel.mm"
include "csca.mm"
include "c0g.mm"
include "cfsupp.mm"
include "wbr.mm"
include "clinc.mm"
include "co.mm"
include "wceq.mm"
include "wa.mm"
include "wral.mm"
include "wi.mm"
include "cmap.mm"
include "clininds.mm"
include "df-lininds.mm"
include "relopabi.mm"

theorem rellininds
  let vf: setvar f
  let vm: setvar m
  let vs: setvar s
  let vx: setvar x
  let vk: setvar k


  assert |- Rel linIndS

  proof
    vs
    cv
    #
    vm
    cv
    #
    cbs
    cfv
    cpw
    wcel
    vf
    cv
    #
    @1
    csca
    cfv
    #
    c0g
    cfv
    #
    cfsupp
    wbr
    @2
    @0
    @1
    clinc
    cfv
    co
    @1
    c0g
    cfv
    wceq
    wa
    vx
    cv
    @2
    cfv
    @4
    wceq
    vx
    @0
    wral
    wi
    vf
    @3
    cbs
    cfv
    @0
    cmap
    co
    wral
    wa
    vs
    vm
    clininds
    vx
    vf
    vm
    vs
    df-lininds
    relopabi
end
