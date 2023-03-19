include "crg.mm"
include "cv.mm"
include "cghm.mm"
include "co.mm"
include "cmgp.mm"
include "cfv.mm"
include "cmhm.mm"
include "cin.mm"
include "crh.mm"
include "dfrhm2.mm"
include "ovex.mm"
include "inex1.mm"
include "fnmpt2i.mm"

theorem rhmfn
  let vr: setvar r
  let vs: setvar s
  let vk: setvar k
  let vx: setvar x


  assert |- RingHom Fn ( Ring X. Ring )

  proof
    vr
    vs
    crg
    crg
    vr
    cv
    #
    vs
    cv
    #
    cghm
    co
    #
    @0
    cmgp
    cfv
    @1
    cmgp
    cfv
    cmhm
    co
    #
    cin
    crh
    vs
    vr
    dfrhm2
    @2
    @3
    @0
    @1
    cghm
    ovex
    inex1
    fnmpt2i
end
