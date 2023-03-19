include "cc0.mm"
include "csin.mm"
include "cfv.mm"
include "cneg.mm"
include "wceq.mm"
include "neg0.mm"
include "fveq2i.mm"
include "cc.mm"
include "wcel.mm"
include "0cn.mm"
include "sinneg.mm"
include "ax-mp.mm"
include "eqtr3i.mm"
include "sincl.mm"
include "eqnegi.mm"
include "mpbi.mm"

theorem sin0



  assert |- ( sin ` 0 ) = 0

  proof
    cc0
    csin
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
    csin
    cfv
    #
    @0
    @1
    @2
    cc0
    csin
    neg0
    fveq2i
    cc0
    cc
    wcel
    #
    @3
    @1
    wceq
    0cn
    cc0
    sinneg
    ax-mp
    eqtr3i
    @0
    @4
    @0
    cc
    wcel
    0cn
    cc0
    sincl
    ax-mp
    eqnegi
    mpbi
end
