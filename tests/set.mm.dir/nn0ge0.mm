include "cn0.mm"
include "wcel.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "clt.mm"
include "wceq.mm"
include "wo.mm"
include "cn.mm"
include "elnn0.mm"
include "nngt0.mm"
include "id.mm"
include "eqcomd.mm"
include "orim12i.mm"
include "sylbi.mm"
include "cr.mm"
include "wb.mm"
include "0re.mm"
include "nn0re.mm"
include "leloe.mm"
include "sylancr.mm"
include "mpbird.mm"

theorem nn0ge0
  let cN: class N


  assert |- ( N e. NN0 -> 0 <_ N )

  proof
    cN
    cn0
    wcel
    #
    cc0
    cN
    cle
    wbr
    #
    cc0
    cN
    clt
    wbr
    #
    cc0
    cN
    wceq
    #
    wo
    #
    @0
    cN
    cn
    wcel
    #
    cN
    cc0
    wceq
    #
    wo
    @4
    cN
    elnn0
    @5
    @2
    @6
    @3
    cN
    nngt0
    @6
    cN
    cc0
    @6
    id
    eqcomd
    orim12i
    sylbi
    @0
    cc0
    cr
    wcel
    cN
    cr
    wcel
    @1
    @4
    wb
    0re
    cN
    nn0re
    cc0
    cN
    leloe
    sylancr
    mpbird
end
