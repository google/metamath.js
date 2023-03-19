include "codd.mm"
include "wcel.mm"
include "c1.mm"
include "cneg.mm"
include "cexp.mm"
include "co.mm"
include "cmin.mm"
include "caddc.mm"
include "cmul.mm"
include "cc.mm"
include "wceq.mm"
include "oddz.mm"
include "zcnd.mm"
include "npcan1.mm"
include "eqcomd.mm"
include "syl.mm"
include "oveq2d.mm"
include "neg1cn.mm"
include "a1i.mm"
include "cc0.mm"
include "wne.mm"
include "neg1ne0.mm"
include "cz.mm"
include "peano2zm.mm"
include "expp1zd.mm"
include "ceven.mm"
include "oddm1eveni.mm"
include "m1expevenALTV.mm"
include "oveq1d.mm"
include "mulid2d.mm"
include "eqtrd.mm"
include "3eqtrd.mm"

theorem m1expoddALTV
  let cN: class N
  let vk: setvar k
  let vx: setvar x


  assert |- ( N e. Odd -> ( -u 1 ^ N ) = -u 1 )

  proof
    cN
    codd
    wcel
    #
    c1
    cneg
    #
    cN
    cexp
    co
    @1
    cN
    c1
    cmin
    co
    #
    c1
    caddc
    co
    #
    cexp
    co
    @1
    @2
    cexp
    co
    #
    @1
    cmul
    co
    #
    @1
    @0
    cN
    @3
    @1
    cexp
    @0
    cN
    cc
    wcel
    #
    cN
    @3
    wceq
    @0
    cN
    cN
    oddz
    #
    zcnd
    @6
    @3
    cN
    cN
    npcan1
    eqcomd
    syl
    oveq2d
    @0
    @1
    @2
    @1
    cc
    wcel
    @0
    neg1cn
    a1i
    #
    @1
    cc0
    wne
    @0
    neg1ne0
    a1i
    @0
    cN
    cz
    wcel
    @2
    cz
    wcel
    @7
    cN
    peano2zm
    syl
    expp1zd
    @0
    @5
    c1
    @1
    cmul
    co
    @1
    @0
    @4
    c1
    @1
    cmul
    @0
    @2
    ceven
    wcel
    @4
    c1
    wceq
    cN
    oddm1eveni
    @2
    m1expevenALTV
    syl
    oveq1d
    @0
    @1
    @8
    mulid2d
    eqtrd
    3eqtrd
end
