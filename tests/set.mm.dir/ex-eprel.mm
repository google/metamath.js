include "c5.mm"
include "c1.mm"
include "cpr.mm"
include "cep.mm"
include "wbr.mm"
include "wcel.mm"
include "cn.mm"
include "5nn.mm"
include "elexi.mm"
include "prid2.mm"
include "prex.mm"
include "epelc.mm"
include "mpbir.mm"

theorem ex-eprel



  assert |- 5 _E { 1 , 5 }

  proof
    c5
    c1
    c5
    cpr
    #
    cep
    wbr
    c5
    @0
    wcel
    c1
    c5
    c5
    cn
    5nn
    elexi
    prid2
    c5
    @0
    c1
    c5
    prex
    epelc
    mpbir
end
