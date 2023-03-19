include "c2.mm"
include "c6.mm"
include "cop.mm"
include "c3.mm"
include "c9.mm"
include "cpr.mm"
include "wceq.mm"
include "cdm.mm"
include "dmeq.mm"
include "cn.mm"
include "6nn.mm"
include "elexi.mm"
include "9nn.mm"
include "dmprop.mm"
include "syl6eq.mm"

theorem ex-dm
  let cF: class F


  assert |- ( F = { <. 2 , 6 >. , <. 3 , 9 >. } -> dom F = { 2 , 3 } )

  proof
    cF
    c2
    c6
    cop
    c3
    c9
    cop
    cpr
    #
    wceq
    cF
    cdm
    @0
    cdm
    c2
    c3
    cpr
    cF
    @0
    dmeq
    c2
    c6
    c3
    c9
    c6
    cn
    6nn
    elexi
    c9
    cn
    9nn
    elexi
    dmprop
    syl6eq
end
