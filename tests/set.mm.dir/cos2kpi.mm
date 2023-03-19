include "cz.mm"
include "wcel.mm"
include "cc0.mm"
include "c2.mm"
include "cpi.mm"
include "cmul.mm"
include "co.mm"
include "caddc.mm"
include "ccos.mm"
include "cfv.mm"
include "c1.mm"
include "cc.mm"
include "zcn.mm"
include "2cn.mm"
include "picn.mm"
include "mulcli.mm"
include "mulcl.mm"
include "sylancl.mm"
include "addid2d.mm"
include "fveq2d.mm"
include "wceq.mm"
include "0cn.mm"
include "cosper.mm"
include "mpan.mm"
include "cos0.mm"
include "syl6eq.mm"
include "eqtr3d.mm"

theorem cos2kpi
  let cK: class K


  assert |- ( K e. ZZ -> ( cos ` ( K x. ( 2 x. _pi ) ) ) = 1 )

  proof
    cK
    cz
    wcel
    #
    cc0
    cK
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
    @2
    ccos
    cfv
    c1
    @0
    @3
    @2
    ccos
    @0
    @2
    @0
    cK
    cc
    wcel
    @1
    cc
    wcel
    @2
    cc
    wcel
    cK
    zcn
    c2
    cpi
    2cn
    picn
    mulcli
    cK
    @1
    mulcl
    sylancl
    addid2d
    fveq2d
    @0
    @4
    cc0
    ccos
    cfv
    #
    c1
    cc0
    cc
    wcel
    @0
    @4
    @5
    wceq
    0cn
    cc0
    cK
    cosper
    mpan
    cos0
    syl6eq
    eqtr3d
end
