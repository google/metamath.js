include "cz.mm"
include "wcel.mm"
include "cc0.mm"
include "clt.mm"
include "wbr.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cle.mm"
include "wb.mm"
include "0z.mm"
include "zltp1le.mm"
include "mpan.mm"
include "wceq.mm"
include "0p1e1.mm"
include "a1i.mm"
include "breq1d.mm"
include "bitrd.mm"

theorem zgt0ge1
  let cZ: class Z


  assert |- ( Z e. ZZ -> ( 0 < Z <-> 1 <_ Z ) )

  proof
    cZ
    cz
    wcel
    #
    cc0
    cZ
    clt
    wbr
    #
    cc0
    c1
    caddc
    co
    #
    cZ
    cle
    wbr
    #
    c1
    cZ
    cle
    wbr
    cc0
    cz
    wcel
    @0
    @1
    @3
    wb
    0z
    cc0
    cZ
    zltp1le
    mpan
    @0
    @2
    c1
    cZ
    cle
    @2
    c1
    wceq
    @0
    0p1e1
    a1i
    breq1d
    bitrd
end
