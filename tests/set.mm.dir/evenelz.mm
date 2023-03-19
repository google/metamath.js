include "c2.mm"
include "cdvds.mm"
include "wbr.mm"
include "cz.mm"
include "wcel.mm"
include "dvdszrcl.mm"
include "simprd.mm"

theorem evenelz
  let cN: class N


  assert |- ( 2 || N -> N e. ZZ )

  proof
    c2
    cN
    cdvds
    wbr
    c2
    cz
    wcel
    cN
    cz
    wcel
    c2
    cN
    dvdszrcl
    simprd
end
