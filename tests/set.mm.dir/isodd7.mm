include "codd.mm"
include "wcel.mm"
include "cz.mm"
include "c2.mm"
include "cdvds.mm"
include "wbr.mm"
include "wn.mm"
include "wa.mm"
include "cgcd.mm"
include "co.mm"
include "c1.mm"
include "wceq.mm"
include "isodd3.mm"
include "cprime.mm"
include "wb.mm"
include "2prm.mm"
include "coprm.mm"
include "mpan.mm"
include "pm5.32i.mm"
include "bitri.mm"

theorem isodd7
  let cZ: class Z
  let vk: setvar k
  let vx: setvar x


  assert |- ( Z e. Odd <-> ( Z e. ZZ /\ ( 2 gcd Z ) = 1 ) )

  proof
    cZ
    codd
    wcel
    cZ
    cz
    wcel
    #
    c2
    cZ
    cdvds
    wbr
    wn
    #
    wa
    @0
    c2
    cZ
    cgcd
    co
    c1
    wceq
    #
    wa
    cZ
    isodd3
    @0
    @1
    @2
    c2
    cprime
    wcel
    @0
    @1
    @2
    wb
    2prm
    c2
    cZ
    coprm
    mpan
    pm5.32i
    bitri
end
