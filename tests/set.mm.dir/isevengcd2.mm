include "cz.mm"
include "wcel.mm"
include "c2.mm"
include "cgcd.mm"
include "co.mm"
include "wceq.mm"
include "cdvds.mm"
include "wbr.mm"
include "cn.mm"
include "wb.mm"
include "2nn.mm"
include "gcdzeq.mm"
include "mpan.mm"
include "bicomd.mm"

theorem isevengcd2
  let cZ: class Z


  assert |- ( Z e. ZZ -> ( 2 || Z <-> ( 2 gcd Z ) = 2 ) )

  proof
    cZ
    cz
    wcel
    #
    c2
    cZ
    cgcd
    co
    c2
    wceq
    #
    c2
    cZ
    cdvds
    wbr
    #
    c2
    cn
    wcel
    @0
    @1
    @2
    wb
    2nn
    c2
    cZ
    gcdzeq
    mpan
    bicomd
end
