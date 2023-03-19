include "cz.mm"
include "wcel.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "c2.mm"
include "cdiv.mm"
include "cmin.mm"
include "peano2zm.mm"
include "peano2z.mm"
include "cc.mm"
include "wceq.mm"
include "zcnd.mm"
include "halfcld.mm"
include "npcan1.mm"
include "syl.mm"
include "eqcomd.mm"
include "eleq1d.mm"
include "syl5ibr.mm"
include "impbid2.mm"
include "zcn.mm"
include "xp1d2m1eqxm1d2.mm"
include "bitrd.mm"

theorem zob
  let cN: class N


  assert |- ( N e. ZZ -> ( ( ( N + 1 ) / 2 ) e. ZZ <-> ( ( N - 1 ) / 2 ) e. ZZ ) )

  proof
    cN
    cz
    wcel
    #
    cN
    c1
    caddc
    co
    #
    c2
    cdiv
    co
    #
    cz
    wcel
    #
    @2
    c1
    cmin
    co
    #
    cz
    wcel
    #
    cN
    c1
    cmin
    co
    c2
    cdiv
    co
    #
    cz
    wcel
    @0
    @3
    @5
    @2
    peano2zm
    @5
    @3
    @0
    @4
    c1
    caddc
    co
    #
    cz
    wcel
    @4
    peano2z
    @0
    @2
    @7
    cz
    @0
    @7
    @2
    @0
    @2
    cc
    wcel
    @7
    @2
    wceq
    @0
    @1
    @0
    @1
    cN
    peano2z
    zcnd
    halfcld
    @2
    npcan1
    syl
    eqcomd
    eleq1d
    syl5ibr
    impbid2
    @0
    @4
    @6
    cz
    @0
    cN
    cc
    wcel
    @4
    @6
    wceq
    cN
    zcn
    cN
    xp1d2m1eqxm1d2
    syl
    eleq1d
    bitrd
end
