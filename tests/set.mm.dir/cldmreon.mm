include "ctopon.mm"
include "cfv.mm"
include "wcel.mm"
include "ccld.mm"
include "cuni.mm"
include "cmre.mm"
include "ctop.mm"
include "topontop.mm"
include "eqid.mm"
include "cldmre.mm"
include "syl.mm"
include "toponuni.mm"
include "fveq2d.mm"
include "eleqtrrd.mm"

theorem cldmreon
  let cB: class B
  let cJ: class J
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vx: setvar x
  let vy: setvar y
  let cV: class V
  let cK: class K


  assert |- ( J e. ( TopOn ` B ) -> ( Clsd ` J ) e. ( Moore ` B ) )

  proof
    cJ
    cB
    ctopon
    cfv
    wcel
    #
    cJ
    ccld
    cfv
    #
    cJ
    cuni
    #
    cmre
    cfv
    #
    cB
    cmre
    cfv
    @0
    cJ
    ctop
    wcel
    @1
    @3
    wcel
    cB
    cJ
    topontop
    cJ
    @2
    @2
    eqid
    cldmre
    syl
    @0
    cB
    @2
    cmre
    cB
    cJ
    toponuni
    fveq2d
    eleqtrrd
end
