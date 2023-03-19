include "cz.mm"
include "wcel.mm"
include "cc0.mm"
include "c2.mm"
include "cpi.mm"
include "cmul.mm"
include "co.mm"
include "caddc.mm"
include "csin.mm"
include "cfv.mm"
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
include "sinper.mm"
include "mpan.mm"
include "sin0.mm"
include "syl6eq.mm"
include "eqtr3d.mm"

theorem sin2kpi
  let cK: class K


  assert |- ( K e. ZZ -> ( sin ` ( K x. ( 2 x. _pi ) ) ) = 0 )

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
    csin
    cfv
    #
    @2
    csin
    cfv
    cc0
    @0
    @3
    @2
    csin
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
    csin
    cfv
    #
    cc0
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
    sinper
    mpan
    sin0
    syl6eq
    eqtr3d
end
