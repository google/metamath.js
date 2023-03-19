include "caddc.mm"
include "co.mm"
include "cfzo.mm"
include "wcel.mm"
include "cz.mm"
include "wa.mm"
include "cc0.mm"
include "cmin.mm"
include "simpl.mm"
include "elfzoel1.mm"
include "adantr.mm"
include "zcnd.mm"
include "addid1d.mm"
include "oveq1d.mm"
include "eleqtrrd.mm"
include "0zd.mm"
include "simpr.mm"
include "fzosubel2.mm"
include "syl13anc.mm"

theorem fzosubel3
  let cA: class A
  let cB: class B
  let cD: class D


  assert |- ( ( A e. ( B ..^ ( B + D ) ) /\ D e. ZZ ) -> ( A - B ) e. ( 0 ..^ D ) )

  proof
    cA
    cB
    cB
    cD
    caddc
    co
    #
    cfzo
    co
    #
    wcel
    #
    cD
    cz
    wcel
    #
    wa
    #
    cA
    cB
    cc0
    caddc
    co
    #
    @0
    cfzo
    co
    #
    wcel
    cB
    cz
    wcel
    #
    cc0
    cz
    wcel
    @3
    cA
    cB
    cmin
    co
    cc0
    cD
    cfzo
    co
    wcel
    @4
    cA
    @1
    @6
    @2
    @3
    simpl
    @4
    @5
    cB
    @0
    cfzo
    @4
    cB
    @4
    cB
    @2
    @7
    @3
    cA
    cB
    @0
    elfzoel1
    adantr
    #
    zcnd
    addid1d
    oveq1d
    eleqtrrd
    @8
    @4
    0zd
    @2
    @3
    simpr
    cA
    cB
    cc0
    cD
    fzosubel2
    syl13anc
end
