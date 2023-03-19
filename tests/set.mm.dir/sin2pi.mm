include "c2.mm"
include "cpi.mm"
include "cmul.mm"
include "co.mm"
include "csin.mm"
include "cfv.mm"
include "ccos.mm"
include "cc0.mm"
include "cc.mm"
include "wcel.mm"
include "wceq.mm"
include "picn.mm"
include "sin2t.mm"
include "ax-mp.mm"
include "c1.mm"
include "cneg.mm"
include "sinpi.mm"
include "cospi.mm"
include "oveq12i.mm"
include "neg1cn.mm"
include "mul02i.mm"
include "eqtri.mm"
include "oveq2i.mm"
include "2t0e0.mm"

theorem sin2pi



  assert |- ( sin ` ( 2 x. _pi ) ) = 0

  proof
    c2
    cpi
    cmul
    co
    csin
    cfv
    #
    c2
    cpi
    csin
    cfv
    #
    cpi
    ccos
    cfv
    #
    cmul
    co
    #
    cmul
    co
    #
    cc0
    cpi
    cc
    wcel
    @0
    @4
    wceq
    picn
    cpi
    sin2t
    ax-mp
    @4
    c2
    cc0
    cmul
    co
    cc0
    @3
    cc0
    c2
    cmul
    @3
    cc0
    c1
    cneg
    #
    cmul
    co
    cc0
    @1
    cc0
    @2
    @5
    cmul
    sinpi
    cospi
    oveq12i
    @5
    neg1cn
    mul02i
    eqtri
    oveq2i
    2t0e0
    eqtri
    eqtri
end
