include "c1.mm"
include "cc0.mm"
include "cdc.mm"
include "c2.mm"
include "cexp.mm"
include "co.mm"
include "cmul.mm"
include "1nn0.mm"
include "0nn0.mm"
include "deccl.mm"
include "nn0cni.mm"
include "sqvali.mm"
include "eqid.mm"
include "mulid2i.mm"
include "mul02i.mm"
include "decmul1.mm"
include "eqtri.mm"

theorem sq10



  assert |- ( ; 1 0 ^ 2 ) = ; ; 1 0 0

  proof
    c1
    cc0
    cdc
    #
    c2
    cexp
    co
    @0
    @0
    cmul
    co
    @0
    cc0
    cdc
    @0
    @0
    c1
    cc0
    1nn0
    0nn0
    deccl
    #
    nn0cni
    #
    sqvali
    c1
    cc0
    @0
    cc0
    @0
    @0
    @1
    1nn0
    0nn0
    @0
    eqid
    0nn0
    @0
    @2
    mulid2i
    @0
    @2
    mul02i
    decmul1
    eqtri
end
