include "cv.mm"
include "cdm.mm"
include "cbs.mm"
include "cfv.mm"
include "wf.mm"
include "cvsca.mm"
include "co.mm"
include "csn.mm"
include "cdif.mm"
include "cima.mm"
include "clspn.mm"
include "wcel.mm"
include "wn.mm"
include "c0g.mm"
include "wral.mm"
include "csca.mm"
include "wsbc.mm"
include "wa.mm"
include "clindf.mm"
include "df-lindf.mm"
include "relopabi.mm"

theorem rellindf
  let vf: setvar f
  let vk: setvar k
  let vs: setvar s
  let vw: setvar w
  let vx: setvar x


  assert |- Rel LIndF

  proof
    vf
    cv
    #
    cdm
    #
    vw
    cv
    #
    cbs
    cfv
    @0
    wf
    vk
    cv
    vx
    cv
    #
    @0
    cfv
    @2
    cvsca
    cfv
    co
    @0
    @1
    @3
    csn
    cdif
    cima
    @2
    clspn
    cfv
    cfv
    wcel
    wn
    vk
    vs
    cv
    #
    cbs
    cfv
    @4
    c0g
    cfv
    csn
    cdif
    wral
    vx
    @1
    wral
    vs
    @2
    csca
    cfv
    wsbc
    wa
    vf
    vw
    clindf
    vx
    vw
    vf
    vk
    vs
    df-lindf
    relopabi
end
