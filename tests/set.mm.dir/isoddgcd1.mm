include "c2.mm"
include "cprime.mm"
include "wcel.mm"
include "cz.mm"
include "cdvds.mm"
include "wbr.mm"
include "wn.mm"
include "cgcd.mm"
include "co.mm"
include "c1.mm"
include "wceq.mm"
include "wb.mm"
include "2prm.mm"
include "coprm.mm"
include "mpan.mm"

theorem isoddgcd1
  let cZ: class Z


  assert |- ( Z e. ZZ -> ( -. 2 || Z <-> ( 2 gcd Z ) = 1 ) )

  proof
    c2
    cprime
    wcel
    cZ
    cz
    wcel
    c2
    cZ
    cdvds
    wbr
    wn
    c2
    cZ
    cgcd
    co
    c1
    wceq
    wb
    2prm
    c2
    cZ
    coprm
    mpan
end
