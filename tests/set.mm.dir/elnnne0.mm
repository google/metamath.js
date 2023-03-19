include "cn.mm"
include "wcel.mm"
include "cn0.mm"
include "cc0.mm"
include "csn.mm"
include "cdif.mm"
include "wne.mm"
include "wa.mm"
include "dfn2.mm"
include "eleq2i.mm"
include "eldifsn.mm"
include "bitri.mm"

theorem elnnne0
  let cN: class N


  assert |- ( N e. NN <-> ( N e. NN0 /\ N =/= 0 ) )

  proof
    cN
    cn
    wcel
    cN
    cn0
    cc0
    csn
    cdif
    #
    wcel
    cN
    cn0
    wcel
    cN
    cc0
    wne
    wa
    cn
    @0
    cN
    dfn2
    eleq2i
    cN
    cn0
    cc0
    eldifsn
    bitri
end
