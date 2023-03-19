include "cn0.mm"
include "wcel.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "wceq.mm"
include "nn0ge0.mm"
include "biantrud.mm"
include "cr.mm"
include "wb.mm"
include "nn0re.mm"
include "0re.mm"
include "letri3.mm"
include "sylancl.mm"
include "bitr4d.mm"

theorem nn0le0eq0
  let cN: class N


  assert |- ( N e. NN0 -> ( N <_ 0 <-> N = 0 ) )

  proof
    cN
    cn0
    wcel
    #
    cN
    cc0
    cle
    wbr
    #
    @1
    cc0
    cN
    cle
    wbr
    #
    wa
    #
    cN
    cc0
    wceq
    #
    @0
    @2
    @1
    cN
    nn0ge0
    biantrud
    @0
    cN
    cr
    wcel
    cc0
    cr
    wcel
    @4
    @3
    wb
    cN
    nn0re
    0re
    cN
    cc0
    letri3
    sylancl
    bitr4d
end
