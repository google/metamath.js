include "c2.mm"
include "cuz.mm"
include "cfv.mm"
include "wcel.mm"
include "cn.mm"
include "c1.mm"
include "clt.mm"
include "wbr.mm"
include "wa.mm"
include "wne.mm"
include "eluz2b2.mm"
include "nngt1ne1.mm"
include "pm5.32i.mm"
include "bitri.mm"

theorem eluz2b3
  let cN: class N


  assert |- ( N e. ( ZZ>= ` 2 ) <-> ( N e. NN /\ N =/= 1 ) )

  proof
    cN
    c2
    cuz
    cfv
    wcel
    cN
    cn
    wcel
    #
    c1
    cN
    clt
    wbr
    #
    wa
    @0
    cN
    c1
    wne
    #
    wa
    cN
    eluz2b2
    @0
    @1
    @2
    cN
    nngt1ne1
    pm5.32i
    bitri
end
