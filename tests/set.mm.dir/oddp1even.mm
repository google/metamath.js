include "cz.mm"
include "wcel.mm"
include "c2.mm"
include "cdvds.mm"
include "wbr.mm"
include "wn.mm"
include "c1.mm"
include "cmin.mm"
include "co.mm"
include "caddc.mm"
include "oddm1even.mm"
include "wb.mm"
include "2z.mm"
include "peano2zm.mm"
include "dvdsadd.mm"
include "sylancr.mm"
include "2cnd.mm"
include "zcn.mm"
include "1cnd.mm"
include "addsub12d.mm"
include "2m1e1.mm"
include "oveq2i.mm"
include "syl6eq.mm"
include "breq2d.mm"
include "3bitrd.mm"

theorem oddp1even
  let cN: class N
  let vk: setvar k
  let vn: setvar n
  let vx: setvar x
  let vy: setvar y


  assert |- ( N e. ZZ -> ( -. 2 || N <-> 2 || ( N + 1 ) ) )

  proof
    cN
    cz
    wcel
    #
    c2
    cN
    cdvds
    wbr
    wn
    c2
    cN
    c1
    cmin
    co
    #
    cdvds
    wbr
    #
    c2
    c2
    @1
    caddc
    co
    #
    cdvds
    wbr
    #
    c2
    cN
    c1
    caddc
    co
    #
    cdvds
    wbr
    cN
    oddm1even
    @0
    c2
    cz
    wcel
    @1
    cz
    wcel
    @2
    @4
    wb
    2z
    cN
    peano2zm
    c2
    @1
    dvdsadd
    sylancr
    @0
    @3
    @5
    c2
    cdvds
    @0
    @3
    cN
    c2
    c1
    cmin
    co
    #
    caddc
    co
    @5
    @0
    c2
    cN
    c1
    @0
    2cnd
    cN
    zcn
    @0
    1cnd
    addsub12d
    @6
    c1
    cN
    caddc
    2m1e1
    oveq2i
    syl6eq
    breq2d
    3bitrd
end
