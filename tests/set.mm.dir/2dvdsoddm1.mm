include "codd.mm"
include "wcel.mm"
include "c2.mm"
include "cdvds.mm"
include "wbr.mm"
include "wn.mm"
include "c1.mm"
include "cmin.mm"
include "co.mm"
include "2ndvdsodd.mm"
include "cz.mm"
include "wb.mm"
include "oddz.mm"
include "oddm1even.mm"
include "syl.mm"
include "mpbid.mm"

theorem 2dvdsoddm1
  let cZ: class Z
  let vk: setvar k
  let vx: setvar x


  assert |- ( Z e. Odd -> 2 || ( Z - 1 ) )

  proof
    cZ
    codd
    wcel
    #
    c2
    cZ
    cdvds
    wbr
    wn
    #
    c2
    cZ
    c1
    cmin
    co
    cdvds
    wbr
    #
    cZ
    2ndvdsodd
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
    oddm1even
    syl
    mpbid
end
