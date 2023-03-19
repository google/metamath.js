include "cz.mm"
include "wcel.mm"
include "c2.mm"
include "cdvds.mm"
include "wbr.mm"
include "wn.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cdiv.mm"
include "oddp1even.mm"
include "cc0.mm"
include "wne.mm"
include "wb.mm"
include "2z.mm"
include "2ne0.mm"
include "peano2z.mm"
include "dvdsval2.mm"
include "mp3an12i.mm"
include "bitrd.mm"

theorem oddp1d2
  let cN: class N


  assert |- ( N e. ZZ -> ( -. 2 || N <-> ( ( N + 1 ) / 2 ) e. ZZ ) )

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
    caddc
    co
    #
    cdvds
    wbr
    #
    @1
    c2
    cdiv
    co
    cz
    wcel
    #
    cN
    oddp1even
    c2
    cz
    wcel
    c2
    cc0
    wne
    @0
    @1
    cz
    wcel
    @2
    @3
    wb
    2z
    2ne0
    cN
    peano2z
    c2
    @1
    dvdsval2
    mp3an12i
    bitrd
end
