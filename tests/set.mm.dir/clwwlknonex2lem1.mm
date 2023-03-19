include "c3.mm"
include "cuz.mm"
include "cfv.mm"
include "wcel.mm"
include "chash.mm"
include "c2.mm"
include "cmin.mm"
include "co.mm"
include "wceq.mm"
include "wa.mm"
include "cc0.mm"
include "caddc.mm"
include "c1.mm"
include "cfzo.mm"
include "cpr.mm"
include "cun.mm"
include "cc.mm"
include "eluzelcn.mm"
include "2cnd.mm"
include "subcld.mm"
include "adantr.mm"
include "wb.mm"
include "eleq1.mm"
include "adantl.mm"
include "mpbird.mm"
include "1cnd.mm"
include "addsubd.mm"
include "oveq2d.mm"
include "oveq1.mm"
include "cn0.mm"
include "uznn0sub.mm"
include "subsub4d.mm"
include "2p1e3.mm"
include "oveq2i.mm"
include "syl6eq.mm"
include "nn0uz.mm"
include "eqcomi.mm"
include "a1i.mm"
include "3eltr4d.mm"
include "eqeltrd.mm"
include "fzosplitpr.mm"
include "syl.mm"
include "npcand.mm"
include "preq2d.mm"
include "uneq2d.mm"
include "3eqtrd.mm"

theorem clwwlknonex2lem1
  let cN: class N
  let cW: class W


  assert |- ( ( N e. ( ZZ>= ` 3 ) /\ ( # ` W ) = ( N - 2 ) ) -> ( 0 ..^ ( ( ( # ` W ) + 2 ) - 1 ) ) = ( ( 0 ..^ ( ( # ` W ) - 1 ) ) u. { ( ( # ` W ) - 1 ) , ( # ` W ) } ) )

  proof
    cN
    c3
    cuz
    cfv
    wcel
    #
    cW
    chash
    cfv
    #
    cN
    c2
    cmin
    co
    #
    wceq
    #
    wa
    #
    cc0
    @1
    c2
    caddc
    co
    c1
    cmin
    co
    #
    cfzo
    co
    cc0
    @1
    c1
    cmin
    co
    #
    c2
    caddc
    co
    #
    cfzo
    co
    #
    cc0
    @6
    cfzo
    co
    #
    @6
    @6
    c1
    caddc
    co
    #
    cpr
    #
    cun
    #
    @9
    @6
    @1
    cpr
    #
    cun
    @4
    @5
    @7
    cc0
    cfzo
    @4
    @1
    c2
    c1
    @4
    @1
    cc
    wcel
    #
    @2
    cc
    wcel
    #
    @0
    @15
    @3
    @0
    cN
    c2
    c3
    cN
    eluzelcn
    #
    @0
    2cnd
    #
    subcld
    adantr
    @3
    @14
    @15
    wb
    @0
    @1
    @2
    cc
    eleq1
    adantl
    mpbird
    #
    @4
    2cnd
    @4
    1cnd
    #
    addsubd
    oveq2d
    @4
    @6
    cc0
    cuz
    cfv
    #
    wcel
    @8
    @12
    wceq
    @4
    @6
    @2
    c1
    cmin
    co
    #
    @20
    @3
    @6
    @21
    wceq
    @0
    @1
    @2
    c1
    cmin
    oveq1
    adantl
    @0
    @21
    @20
    wcel
    @3
    @0
    cN
    c3
    cmin
    co
    #
    cn0
    @21
    @20
    c3
    cN
    uznn0sub
    @0
    @21
    cN
    c2
    c1
    caddc
    co
    #
    cmin
    co
    @22
    @0
    cN
    c2
    c1
    @16
    @17
    @0
    1cnd
    subsub4d
    @23
    c3
    cN
    cmin
    2p1e3
    oveq2i
    syl6eq
    @20
    cn0
    wceq
    @0
    cn0
    @20
    nn0uz
    eqcomi
    a1i
    3eltr4d
    adantr
    eqeltrd
    cc0
    @6
    fzosplitpr
    syl
    @4
    @11
    @13
    @9
    @4
    @10
    @1
    @6
    @4
    @1
    c1
    @18
    @19
    npcand
    preq2d
    uneq2d
    3eqtrd
end
