include "crecs.mm"
include "eqid.mm"
include "tfr1.mm"

theorem recsfnon
  let cF: class F


  assert |- recs ( F ) Fn On

  proof
    cF
    crecs
    #
    cF
    @0
    eqid
    tfr1
end
