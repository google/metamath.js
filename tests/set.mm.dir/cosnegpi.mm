include "cpi.mm"
include "cneg.mm"
include "ccos.mm"
include "cfv.mm"
include "c1.mm"
include "c2.mm"
include "cmul.mm"
include "co.mm"
include "caddc.mm"
include "cmin.mm"
include "2cn.mm"
include "picn.mm"
include "mulcli.mm"
include "mulm1i.mm"
include "oveq2i.mm"
include "negsubi.mm"
include "cc.mm"
include "wcel.mm"
include "wceq.mm"
include "sub2times.mm"
include "ax-mp.mm"
include "3eqtrri.mm"
include "fveq2i.mm"
include "cz.mm"
include "neg1z.mm"
include "cosper.mm"
include "mp2an.mm"
include "cospi.mm"
include "3eqtri.mm"

theorem cosnegpi
  let vk: setvar k
  let vx: setvar x


  assert |- ( cos ` -u _pi ) = -u 1

  proof
    cpi
    cneg
    #
    ccos
    cfv
    cpi
    c1
    cneg
    #
    c2
    cpi
    cmul
    co
    #
    cmul
    co
    #
    caddc
    co
    #
    ccos
    cfv
    #
    cpi
    ccos
    cfv
    #
    @1
    @0
    @4
    ccos
    @4
    cpi
    @2
    cneg
    #
    caddc
    co
    cpi
    @2
    cmin
    co
    #
    @0
    @3
    @7
    cpi
    caddc
    @2
    c2
    cpi
    2cn
    picn
    mulcli
    #
    mulm1i
    oveq2i
    cpi
    @2
    picn
    @9
    negsubi
    cpi
    cc
    wcel
    #
    @8
    @0
    wceq
    picn
    cpi
    sub2times
    ax-mp
    3eqtrri
    fveq2i
    @10
    @1
    cz
    wcel
    @5
    @6
    wceq
    picn
    neg1z
    cpi
    @1
    cosper
    mp2an
    cospi
    3eqtri
end
