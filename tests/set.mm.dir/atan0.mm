include "cc0.mm"
include "catan.mm"
include "cfv.mm"
include "cneg.mm"
include "wceq.mm"
include "neg0.mm"
include "fveq2i.mm"
include "cr.mm"
include "wcel.mm"
include "cdm.mm"
include "0re.mm"
include "atanre.mm"
include "atanneg.mm"
include "mp2b.mm"
include "eqtr3i.mm"
include "cc.mm"
include "atancl.mm"
include "eqnegi.mm"
include "mpbi.mm"

theorem atan0



  assert |- ( arctan ` 0 ) = 0

  proof
    cc0
    catan
    cfv
    #
    @0
    cneg
    #
    wceq
    @0
    cc0
    wceq
    cc0
    cneg
    #
    catan
    cfv
    #
    @0
    @1
    @2
    cc0
    catan
    neg0
    fveq2i
    cc0
    cr
    wcel
    #
    cc0
    catan
    cdm
    wcel
    #
    @3
    @1
    wceq
    0re
    cc0
    atanre
    #
    cc0
    atanneg
    mp2b
    eqtr3i
    @0
    @4
    @5
    @0
    cc
    wcel
    0re
    @6
    cc0
    atancl
    mp2b
    eqnegi
    mpbi
end
