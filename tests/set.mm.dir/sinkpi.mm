include "cz.mm"
include "wcel.mm"
include "cc0.mm"
include "cpi.mm"
include "cmul.mm"
include "co.mm"
include "caddc.mm"
include "csin.mm"
include "cfv.mm"
include "cc.mm"
include "zcn.mm"
include "picn.mm"
include "mulcl.mm"
include "sylancl.mm"
include "addid2d.mm"
include "fveq2d.mm"
include "0cn.mm"
include "addcl.mm"
include "sylancr.mm"
include "sincld.mm"
include "cabs.mm"
include "wceq.mm"
include "abssinper.mm"
include "mpan.mm"
include "sin0.mm"
include "fveq2i.mm"
include "abs0.mm"
include "eqtri.mm"
include "syl6eq.mm"
include "abs00d.mm"
include "eqtr3d.mm"

theorem sinkpi
  let cK: class K


  assert |- ( K e. ZZ -> ( sin ` ( K x. _pi ) ) = 0 )

  proof
    cK
    cz
    wcel
    #
    cc0
    cK
    cpi
    cmul
    co
    #
    caddc
    co
    #
    csin
    cfv
    #
    @1
    csin
    cfv
    cc0
    @0
    @2
    @1
    csin
    @0
    @1
    @0
    cK
    cc
    wcel
    cpi
    cc
    wcel
    @1
    cc
    wcel
    #
    cK
    zcn
    picn
    cK
    cpi
    mulcl
    sylancl
    #
    addid2d
    fveq2d
    @0
    @3
    @0
    @2
    @0
    cc0
    cc
    wcel
    #
    @4
    @2
    cc
    wcel
    0cn
    @5
    cc0
    @1
    addcl
    sylancr
    sincld
    @0
    @3
    cabs
    cfv
    #
    cc0
    csin
    cfv
    #
    cabs
    cfv
    #
    cc0
    @6
    @0
    @7
    @9
    wceq
    0cn
    cc0
    cK
    abssinper
    mpan
    @9
    cc0
    cabs
    cfv
    cc0
    @8
    cc0
    cabs
    sin0
    fveq2i
    abs0
    eqtri
    syl6eq
    abs00d
    eqtr3d
end
