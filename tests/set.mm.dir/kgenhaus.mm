include "cha.mm"
include "wcel.mm"
include "ckgen.mm"
include "cfv.mm"
include "cuni.mm"
include "ctopon.mm"
include "wss.mm"
include "ctop.mm"
include "haustop.mm"
include "eqid.mm"
include "toptopon.mm"
include "sylib.mm"
include "kgentopon.mm"
include "syl.mm"
include "kgenss.mm"
include "sshaus.mm"
include "mpd3an23.mm"

theorem kgenhaus
  let cJ: class J
  let vj: setvar j
  let vk: setvar k
  let vx: setvar x
  let cK: class K


  assert |- ( J e. Haus -> ( kGen ` J ) e. Haus )

  proof
    cJ
    cha
    wcel
    #
    cJ
    ckgen
    cfv
    #
    cJ
    cuni
    #
    ctopon
    cfv
    #
    wcel
    #
    cJ
    @1
    wss
    #
    @1
    cha
    wcel
    @0
    cJ
    @3
    wcel
    #
    @4
    @0
    cJ
    ctop
    wcel
    #
    @6
    cJ
    haustop
    #
    cJ
    @2
    @2
    eqid
    #
    toptopon
    sylib
    cJ
    @2
    kgentopon
    syl
    @0
    @7
    @5
    @8
    cJ
    kgenss
    syl
    cJ
    @1
    @2
    @9
    sshaus
    mpd3an23
end
