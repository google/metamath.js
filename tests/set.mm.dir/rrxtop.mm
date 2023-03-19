include "wcel.mm"
include "crrx.mm"
include "cfv.mm"
include "ctps.mm"
include "ctop.mm"
include "rrxtps.mm"
include "tpstop.mm"
include "syl.mm"

theorem rrxtop
  let cI: class I
  let cJ: class J
  let cV: class V
  let vk: setvar k
  let vx: setvar x
  assume rrxtop.1: |- J = ( TopOpen ` ( RR^ ` I ) )


  assert |- ( I e. V -> J e. Top )

  proof
    cI
    cV
    wcel
    cI
    crrx
    cfv
    #
    ctps
    wcel
    cJ
    ctop
    wcel
    cI
    cV
    rrxtps
    cJ
    @0
    rrxtop.1
    tpstop
    syl
end
