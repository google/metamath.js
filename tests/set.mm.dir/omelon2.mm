include "com.mm"
include "con0.mm"
include "wcel.mm"
include "cvv.mm"
include "wn.mm"
include "wceq.mm"
include "omon.mm"
include "ori.mm"
include "onprc.mm"
include "eleq1.mm"
include "mtbiri.mm"
include "syl.mm"
include "con4i.mm"

theorem omelon2



  assert |- ( _om e. _V -> _om e. On )

  proof
    com
    con0
    wcel
    #
    com
    cvv
    wcel
    #
    @0
    wn
    com
    con0
    wceq
    #
    @1
    wn
    @0
    @2
    omon
    ori
    @2
    @1
    con0
    cvv
    wcel
    onprc
    com
    con0
    cvv
    eleq1
    mtbiri
    syl
    con4i
end
