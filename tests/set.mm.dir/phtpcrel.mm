include "cv.mm"
include "cpr.mm"
include "cii.mm"
include "ccn.mm"
include "co.mm"
include "wss.mm"
include "cphtpy.mm"
include "cfv.mm"
include "c0.mm"
include "wne.mm"
include "wa.mm"
include "ctop.mm"
include "cphtpc.mm"
include "df-phtpc.mm"
include "relmptopab.mm"

theorem phtpcrel
  let cJ: class J
  let vf: setvar f
  let vx: setvar x
  let vg: setvar g


  assert |- Rel ( ~=ph ` J )

  proof
    vf
    cv
    #
    vg
    cv
    #
    cpr
    cii
    vx
    cv
    #
    ccn
    co
    wss
    @0
    @1
    @2
    cphtpy
    cfv
    co
    c0
    wne
    wa
    vx
    vf
    vg
    ctop
    cJ
    cphtpc
    vx
    vf
    vg
    df-phtpc
    relmptopab
end
