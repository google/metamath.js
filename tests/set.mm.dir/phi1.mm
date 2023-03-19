include "c1.mm"
include "cphi.mm"
include "cfv.mm"
include "csn.mm"
include "wcel.mm"
include "wceq.mm"
include "cfz.mm"
include "co.mm"
include "cn.mm"
include "1nn.mm"
include "phicl2.mm"
include "ax-mp.mm"
include "cz.mm"
include "1z.mm"
include "fzsn.mm"
include "eleqtri.mm"
include "elsni.mm"

theorem phi1



  assert |- ( phi ` 1 ) = 1

  proof
    c1
    cphi
    cfv
    #
    c1
    csn
    #
    wcel
    @0
    c1
    wceq
    @0
    c1
    c1
    cfz
    co
    #
    @1
    c1
    cn
    wcel
    @0
    @2
    wcel
    1nn
    c1
    phicl2
    ax-mp
    c1
    cz
    wcel
    @2
    @1
    wceq
    1z
    c1
    fzsn
    ax-mp
    eleqtri
    @0
    c1
    elsni
    ax-mp
end
