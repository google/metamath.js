include "c1.mm"
include "clgam.mm"
include "cfv.mm"
include "ce.mm"
include "cc0.mm"
include "cgam.mm"
include "lgam1.mm"
include "fveq2i.mm"
include "cc.mm"
include "cz.mm"
include "cn.mm"
include "cdif.mm"
include "wcel.mm"
include "wceq.mm"
include "wn.mm"
include "ax-1cn.mm"
include "1nn.mm"
include "eldifn.mm"
include "mt2.mm"
include "eldif.mm"
include "mpbir2an.mm"
include "eflgam.mm"
include "ax-mp.mm"
include "ef0.mm"
include "3eqtr3i.mm"

theorem gam1



  assert |- ( _G ` 1 ) = 1

  proof
    c1
    clgam
    cfv
    #
    ce
    cfv
    #
    cc0
    ce
    cfv
    c1
    cgam
    cfv
    #
    c1
    @0
    cc0
    ce
    lgam1
    fveq2i
    c1
    cc
    cz
    cn
    cdif
    #
    cdif
    wcel
    #
    @1
    @2
    wceq
    @4
    c1
    cc
    wcel
    c1
    @3
    wcel
    #
    wn
    ax-1cn
    @5
    c1
    cn
    wcel
    1nn
    c1
    cz
    cn
    eldifn
    mt2
    c1
    cc
    @3
    eldif
    mpbir2an
    c1
    eflgam
    ax-mp
    ef0
    3eqtr3i
end
