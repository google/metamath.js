include "c0.mm"
include "crrx.mm"
include "cfv.mm"
include "ctopn.mm"
include "csn.mm"
include "cpw.mm"
include "cpr.mm"
include "rrxtopn0.mm"
include "pwsn.mm"
include "eqtri.mm"

theorem rrxtopn0b
  let vk: setvar k
  let vx: setvar x


  assert |- ( TopOpen ` ( RR^ ` (/) ) ) = { (/) , { (/) } }

  proof
    c0
    crrx
    cfv
    ctopn
    cfv
    c0
    csn
    #
    cpw
    c0
    @0
    cpr
    rrxtopn0
    c0
    pwsn
    eqtri
end
