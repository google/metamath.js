include "ceven.mm"
include "wcel.mm"
include "cz.mm"
include "c2.mm"
include "cdvds.mm"
include "wbr.mm"
include "wa.mm"
include "cgcd.mm"
include "co.mm"
include "wceq.mm"
include "iseven2.mm"
include "cn.mm"
include "wb.mm"
include "2nn.mm"
include "gcdzeq.mm"
include "mpan.mm"
include "bicomd.mm"
include "pm5.32i.mm"
include "bitri.mm"

theorem iseven5
  let cZ: class Z
  let vk: setvar k
  let vx: setvar x


  assert |- ( Z e. Even <-> ( Z e. ZZ /\ ( 2 gcd Z ) = 2 ) )

  proof
    cZ
    ceven
    wcel
    cZ
    cz
    wcel
    #
    c2
    cZ
    cdvds
    wbr
    #
    wa
    @0
    c2
    cZ
    cgcd
    co
    c2
    wceq
    #
    wa
    cZ
    iseven2
    @0
    @1
    @2
    @0
    @2
    @1
    c2
    cn
    wcel
    @0
    @2
    @1
    wb
    2nn
    c2
    cZ
    gcdzeq
    mpan
    bicomd
    pm5.32i
    bitri
end
