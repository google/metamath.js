include "codd.mm"
include "wcel.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "c2.mm"
include "cdiv.mm"
include "cz.mm"
include "cmin.mm"
include "oddp1div2z.mm"
include "wb.mm"
include "oddz.mm"
include "zob.mm"
include "syl.mm"
include "mpbid.mm"

theorem oddm1div2z
  let cZ: class Z
  let vk: setvar k
  let vx: setvar x


  assert |- ( Z e. Odd -> ( ( Z - 1 ) / 2 ) e. ZZ )

  proof
    cZ
    codd
    wcel
    #
    cZ
    c1
    caddc
    co
    c2
    cdiv
    co
    cz
    wcel
    #
    cZ
    c1
    cmin
    co
    c2
    cdiv
    co
    cz
    wcel
    #
    cZ
    oddp1div2z
    @0
    cZ
    cz
    wcel
    @1
    @2
    wb
    cZ
    oddz
    cZ
    zob
    syl
    mpbid
end
