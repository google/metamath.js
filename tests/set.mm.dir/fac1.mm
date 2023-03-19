include "c1.mm"
include "cfa.mm"
include "cfv.mm"
include "cmul.mm"
include "cid.mm"
include "cseq.mm"
include "cn.mm"
include "wcel.mm"
include "wceq.mm"
include "1nn.mm"
include "facnn.mm"
include "ax-mp.mm"
include "cz.mm"
include "1z.mm"
include "seq1.mm"
include "fvi.mm"
include "3eqtri.mm"

theorem fac1



  assert |- ( ! ` 1 ) = 1

  proof
    c1
    cfa
    cfv
    #
    c1
    cmul
    cid
    c1
    cseq
    cfv
    #
    c1
    cid
    cfv
    #
    c1
    c1
    cn
    wcel
    #
    @0
    @1
    wceq
    1nn
    c1
    facnn
    ax-mp
    c1
    cz
    wcel
    @1
    @2
    wceq
    1z
    cmul
    cid
    c1
    seq1
    ax-mp
    @3
    @2
    c1
    wceq
    1nn
    c1
    cn
    fvi
    ax-mp
    3eqtri
end
