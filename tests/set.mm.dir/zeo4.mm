include "c2.mm"
include "cdvds.mm"
include "wbr.mm"
include "wn.mm"
include "wb.mm"
include "cz.mm"
include "wcel.mm"
include "notnotb.mm"
include "a1i.mm"

theorem zeo4
  let cN: class N


  assert |- ( N e. ZZ -> ( 2 || N <-> -. -. 2 || N ) )

  proof
    c2
    cN
    cdvds
    wbr
    #
    @0
    wn
    wn
    wb
    cN
    cz
    wcel
    @0
    notnotb
    a1i
end
