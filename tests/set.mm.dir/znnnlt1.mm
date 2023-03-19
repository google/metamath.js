include "cz.mm"
include "wcel.mm"
include "cn.mm"
include "wn.mm"
include "c1.mm"
include "cle.mm"
include "wbr.mm"
include "clt.mm"
include "elnnz1.mm"
include "baib.mm"
include "notbid.mm"
include "cr.mm"
include "wb.mm"
include "zre.mm"
include "1re.mm"
include "ltnle.mm"
include "sylancl.mm"
include "bitr4d.mm"

theorem znnnlt1
  let cN: class N


  assert |- ( N e. ZZ -> ( -. N e. NN <-> N < 1 ) )

  proof
    cN
    cz
    wcel
    #
    cN
    cn
    wcel
    #
    wn
    c1
    cN
    cle
    wbr
    #
    wn
    #
    cN
    c1
    clt
    wbr
    #
    @0
    @1
    @2
    @1
    @0
    @2
    cN
    elnnz1
    baib
    notbid
    @0
    cN
    cr
    wcel
    c1
    cr
    wcel
    @4
    @3
    wb
    cN
    zre
    1re
    cN
    c1
    ltnle
    sylancl
    bitr4d
end
