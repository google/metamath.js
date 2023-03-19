include "c2.mm"
include "cz.mm"
include "wcel.mm"
include "cc0.mm"
include "wne.mm"
include "cdvds.mm"
include "wbr.mm"
include "cdiv.mm"
include "co.mm"
include "wb.mm"
include "2z.mm"
include "2ne0.mm"
include "dvdsval2.mm"
include "mp3an12.mm"

theorem evend2
  let cN: class N


  assert |- ( N e. ZZ -> ( 2 || N <-> ( N / 2 ) e. ZZ ) )

  proof
    c2
    cz
    wcel
    c2
    cc0
    wne
    cN
    cz
    wcel
    c2
    cN
    cdvds
    wbr
    cN
    c2
    cdiv
    co
    cz
    wcel
    wb
    2z
    2ne0
    c2
    cN
    dvdsval2
    mp3an12
end
