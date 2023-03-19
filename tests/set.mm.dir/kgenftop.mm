include "ctop.mm"
include "wcel.mm"
include "ckgen.mm"
include "cfv.mm"
include "cuni.mm"
include "ctopon.mm"
include "eqid.mm"
include "toptopon.mm"
include "kgentopon.mm"
include "sylbi.mm"
include "topontop.mm"
include "syl.mm"

theorem kgenftop
  let cJ: class J
  let vj: setvar j
  let vk: setvar k
  let vx: setvar x
  let cK: class K


  assert |- ( J e. Top -> ( kGen ` J ) e. Top )

  proof
    cJ
    ctop
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
    @1
    ctop
    wcel
    @0
    cJ
    @3
    wcel
    @4
    cJ
    @2
    @2
    eqid
    toptopon
    cJ
    @2
    kgentopon
    sylbi
    @2
    @1
    topontop
    syl
end
