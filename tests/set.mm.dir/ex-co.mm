include "cc0.mm"
include "ccos.mm"
include "cfv.mm"
include "ce.mm"
include "c1.mm"
include "ccom.mm"
include "ceu.mm"
include "cos0.mm"
include "fveq2i.mm"
include "cc.mm"
include "wf.mm"
include "wcel.mm"
include "wceq.mm"
include "cosf.mm"
include "0cn.mm"
include "fvco3.mm"
include "mp2an.mm"
include "df-e.mm"
include "3eqtr4i.mm"

theorem ex-co



  assert |- ( ( exp o. cos ) ` 0 ) = _e

  proof
    cc0
    ccos
    cfv
    #
    ce
    cfv
    #
    c1
    ce
    cfv
    cc0
    ce
    ccos
    ccom
    cfv
    #
    ceu
    @0
    c1
    ce
    cos0
    fveq2i
    cc
    cc
    ccos
    wf
    cc0
    cc
    wcel
    @2
    @1
    wceq
    cosf
    0cn
    cc
    cc
    cc0
    ce
    ccos
    fvco3
    mp2an
    df-e
    3eqtr4i
end
