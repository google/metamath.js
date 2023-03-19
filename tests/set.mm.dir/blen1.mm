include "c1.mm"
include "cn.mm"
include "wcel.mm"
include "cblen.mm"
include "cfv.mm"
include "wceq.mm"
include "1nn.mm"
include "c2.mm"
include "clogb.mm"
include "co.mm"
include "cfl.mm"
include "caddc.mm"
include "blennn.mm"
include "cc0.mm"
include "cc.mm"
include "wne.mm"
include "2cn.mm"
include "2ne0.mm"
include "1ne2.mm"
include "necomi.mm"
include "logb1.mm"
include "mp3an.mm"
include "fveq2i.mm"
include "cz.mm"
include "0z.mm"
include "flid.mm"
include "ax-mp.mm"
include "eqtri.mm"
include "a1i.mm"
include "oveq1d.mm"
include "0p1e1.mm"
include "syl6eq.mm"
include "eqtrd.mm"

theorem blen1
  let vk: setvar k
  let vx: setvar x


  assert |- ( #b ` 1 ) = 1

  proof
    c1
    cn
    wcel
    #
    c1
    cblen
    cfv
    #
    c1
    wceq
    1nn
    @0
    @1
    c2
    c1
    clogb
    co
    #
    cfl
    cfv
    #
    c1
    caddc
    co
    #
    c1
    c1
    blennn
    @0
    @4
    cc0
    c1
    caddc
    co
    c1
    @0
    @3
    cc0
    c1
    caddc
    @3
    cc0
    wceq
    @0
    @3
    cc0
    cfl
    cfv
    #
    cc0
    @2
    cc0
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
    cc0
    wceq
    2cn
    2ne0
    c1
    c2
    1ne2
    necomi
    c2
    logb1
    mp3an
    fveq2i
    cc0
    cz
    wcel
    @5
    cc0
    wceq
    0z
    cc0
    flid
    ax-mp
    eqtri
    a1i
    oveq1d
    0p1e1
    syl6eq
    eqtrd
    ax-mp
end
