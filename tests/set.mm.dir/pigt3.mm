include "c3.mm"
include "cpi.mm"
include "clt.mm"
include "wbr.mm"
include "c6.mm"
include "cdiv.mm"
include "co.mm"
include "csin.mm"
include "cfv.mm"
include "c1.mm"
include "c2.mm"
include "cmul.mm"
include "wceq.mm"
include "ccos.mm"
include "csqrt.mm"
include "sincos6thpi.mm"
include "simpli.mm"
include "cc.mm"
include "wcel.mm"
include "cc0.mm"
include "wne.mm"
include "wa.mm"
include "ax-1cn.mm"
include "2cnne0.mm"
include "3cn.mm"
include "3ne0.mm"
include "pm3.2i.mm"
include "divcan5.mm"
include "mp3an.mm"
include "3t1e3.mm"
include "3t2e6.mm"
include "oveq12i.mm"
include "3eqtr2i.mm"
include "crp.mm"
include "pire.mm"
include "pipos.mm"
include "elrpii.mm"
include "6re.mm"
include "6pos.mm"
include "rpdivcl.mm"
include "mp2an.mm"
include "sinltx.mm"
include "ax-mp.mm"
include "eqbrtrri.mm"
include "3re.mm"
include "ltdiv1ii.mm"
include "mpbir.mm"

theorem pigt3



  assert |- 3 < _pi

  proof
    c3
    cpi
    clt
    wbr
    c3
    c6
    cdiv
    co
    #
    cpi
    c6
    cdiv
    co
    #
    clt
    wbr
    @1
    csin
    cfv
    #
    @0
    @1
    clt
    @2
    c1
    c2
    cdiv
    co
    #
    c3
    c1
    cmul
    co
    #
    c3
    c2
    cmul
    co
    #
    cdiv
    co
    #
    @0
    @2
    @3
    wceq
    @1
    ccos
    cfv
    c3
    csqrt
    cfv
    c2
    cdiv
    co
    wceq
    sincos6thpi
    simpli
    c1
    cc
    wcel
    c2
    cc
    wcel
    c2
    cc0
    wne
    wa
    c3
    cc
    wcel
    #
    c3
    cc0
    wne
    #
    wa
    @6
    @3
    wceq
    ax-1cn
    2cnne0
    @7
    @8
    3cn
    3ne0
    pm3.2i
    c1
    c2
    c3
    divcan5
    mp3an
    @4
    c3
    @5
    c6
    cdiv
    3t1e3
    3t2e6
    oveq12i
    3eqtr2i
    @1
    crp
    wcel
    #
    @2
    @1
    clt
    wbr
    cpi
    crp
    wcel
    c6
    crp
    wcel
    @9
    cpi
    pire
    pipos
    elrpii
    c6
    6re
    6pos
    elrpii
    cpi
    c6
    rpdivcl
    mp2an
    @1
    sinltx
    ax-mp
    eqbrtrri
    c3
    cpi
    c6
    3re
    pire
    6re
    6pos
    ltdiv1ii
    mpbir
end
