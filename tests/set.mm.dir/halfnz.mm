include "c2.mm"
include "cr.mm"
include "wcel.mm"
include "c1.mm"
include "clt.mm"
include "wbr.mm"
include "cdiv.mm"
include "co.mm"
include "cz.mm"
include "wn.mm"
include "2re.mm"
include "1lt2.mm"
include "recnz.mm"
include "mp2an.mm"

theorem halfnz



  assert |- -. ( 1 / 2 ) e. ZZ

  proof
    c2
    cr
    wcel
    c1
    c2
    clt
    wbr
    c1
    c2
    cdiv
    co
    cz
    wcel
    wn
    2re
    1lt2
    c2
    recnz
    mp2an
end
