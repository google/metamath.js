include "ceven.mm"
include "wcel.mm"
include "c1.mm"
include "cmin.mm"
include "co.mm"
include "cz.mm"
include "caddc.mm"
include "c2.mm"
include "cdiv.mm"
include "codd.mm"
include "evenz.mm"
include "peano2zm.mm"
include "syl.mm"
include "wa.mm"
include "iseven.mm"
include "cc.mm"
include "wceq.mm"
include "zcn.mm"
include "npcan1.mm"
include "eqcomd.mm"
include "oveq1d.mm"
include "eleq1d.mm"
include "biimpa.mm"
include "sylbi.mm"
include "isodd.mm"
include "sylanbrc.mm"

theorem evenm1odd
  let cZ: class Z
  let vk: setvar k
  let vx: setvar x


  assert |- ( Z e. Even -> ( Z - 1 ) e. Odd )

  proof
    cZ
    ceven
    wcel
    #
    cZ
    c1
    cmin
    co
    #
    cz
    wcel
    #
    @1
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
    @1
    codd
    wcel
    @0
    cZ
    cz
    wcel
    #
    @2
    cZ
    evenz
    cZ
    peano2zm
    syl
    @0
    @6
    cZ
    c2
    cdiv
    co
    #
    cz
    wcel
    #
    wa
    @5
    cZ
    iseven
    @6
    @8
    @5
    @6
    @7
    @4
    cz
    @6
    cZ
    @3
    c2
    cdiv
    @6
    @3
    cZ
    @6
    cZ
    cc
    wcel
    @3
    cZ
    wceq
    cZ
    zcn
    cZ
    npcan1
    syl
    eqcomd
    oveq1d
    eleq1d
    biimpa
    sylbi
    @1
    isodd
    sylanbrc
end
