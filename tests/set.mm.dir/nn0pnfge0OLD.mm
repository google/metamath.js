include "cn0.mm"
include "wcel.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "cpnf.mm"
include "wceq.mm"
include "nn0ge0.mm"
include "0lepnf.mm"
include "breq2.mm"
include "mpbiri.mm"
include "jaoi.mm"

theorem nn0pnfge0OLD
  let cN: class N


  assert |- ( ( N e. NN0 \/ N = +oo ) -> 0 <_ N )

  proof
    cN
    cn0
    wcel
    cc0
    cN
    cle
    wbr
    #
    cN
    cpnf
    wceq
    #
    cN
    nn0ge0
    @1
    @0
    cc0
    cpnf
    cle
    wbr
    0lepnf
    cN
    cpnf
    cc0
    cle
    breq2
    mpbiri
    jaoi
end
