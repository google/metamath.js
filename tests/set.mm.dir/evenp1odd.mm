include "ceven.mm"
include "wcel.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cz.mm"
include "cmin.mm"
include "c2.mm"
include "cdiv.mm"
include "codd.mm"
include "evenz.mm"
include "peano2zd.mm"
include "wa.mm"
include "iseven.mm"
include "cc.mm"
include "wceq.mm"
include "zcn.mm"
include "pncan1.mm"
include "syl.mm"
include "eqcomd.mm"
include "oveq1d.mm"
include "eleq1d.mm"
include "biimpa.mm"
include "sylbi.mm"
include "isodd2.mm"
include "sylanbrc.mm"

theorem evenp1odd
  let cZ: class Z
  let vk: setvar k
  let vx: setvar x


  assert |- ( Z e. Even -> ( Z + 1 ) e. Odd )

  proof
    cZ
    ceven
    wcel
    #
    cZ
    c1
    caddc
    co
    #
    cz
    wcel
    @1
    c1
    cmin
    co
    #
    c2
    cdiv
    co
    #
    cz
    wcel
    #
    @1
    codd
    wcel
    @0
    cZ
    cZ
    evenz
    peano2zd
    @0
    cZ
    cz
    wcel
    #
    cZ
    c2
    cdiv
    co
    #
    cz
    wcel
    #
    wa
    @4
    cZ
    iseven
    @5
    @7
    @4
    @5
    @6
    @3
    cz
    @5
    cZ
    @2
    c2
    cdiv
    @5
    @2
    cZ
    @5
    cZ
    cc
    wcel
    @2
    cZ
    wceq
    cZ
    zcn
    cZ
    pncan1
    syl
    eqcomd
    oveq1d
    eleq1d
    biimpa
    sylbi
    @1
    isodd2
    sylanbrc
end
