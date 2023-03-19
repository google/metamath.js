include "c2.mm"
include "cn.mm"
include "wcel.mm"
include "cblen.mm"
include "cfv.mm"
include "wceq.mm"
include "2nn.mm"
include "clogb.mm"
include "co.mm"
include "cfl.mm"
include "c1.mm"
include "caddc.mm"
include "blennn.mm"
include "cc.mm"
include "cc0.mm"
include "wne.mm"
include "2cn.mm"
include "2ne0.mm"
include "1ne2.mm"
include "necomi.mm"
include "logbid1.mm"
include "mp3an.mm"
include "fveq2i.mm"
include "cz.mm"
include "1z.mm"
include "flid.mm"
include "ax-mp.mm"
include "eqtri.mm"
include "a1i.mm"
include "oveq1d.mm"
include "1p1e2.mm"
include "3eqtrd.mm"

theorem blen2
  let vk: setvar k
  let vx: setvar x


  assert |- ( #b ` 2 ) = 2

  proof
    c2
    cn
    wcel
    #
    c2
    cblen
    cfv
    #
    c2
    wceq
    2nn
    @0
    @1
    c2
    c2
    clogb
    co
    #
    cfl
    cfv
    #
    c1
    caddc
    co
    c1
    c1
    caddc
    co
    #
    c2
    c2
    blennn
    @0
    @3
    c1
    c1
    caddc
    @3
    c1
    wceq
    @0
    @3
    c1
    cfl
    cfv
    #
    c1
    @2
    c1
    cfl
    c2
    cc
    wcel
    c2
    cc0
    wne
    c2
    c1
    wne
    @2
    c1
    wceq
    2cn
    2ne0
    c1
    c2
    1ne2
    necomi
    c2
    logbid1
    mp3an
    fveq2i
    c1
    cz
    wcel
    @5
    c1
    wceq
    1z
    c1
    flid
    ax-mp
    eqtri
    a1i
    oveq1d
    @4
    c2
    wceq
    @0
    1p1e2
    a1i
    3eqtrd
    ax-mp
end
