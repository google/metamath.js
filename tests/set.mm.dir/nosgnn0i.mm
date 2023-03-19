include "c0.mm"
include "wceq.mm"
include "c1o.mm"
include "c2o.mm"
include "cpr.mm"
include "wcel.mm"
include "nosgnn0.mm"
include "eleq1.mm"
include "mpbiri.mm"
include "mto.mm"
include "neir.mm"

theorem nosgnn0i
  let cX: class X
  assume nosgnn0i.1: |- X e. { 1o , 2o }


  assert |- (/) =/= X

  proof
    c0
    cX
    c0
    cX
    wceq
    #
    c0
    c1o
    c2o
    cpr
    #
    wcel
    #
    nosgnn0
    @0
    @2
    cX
    @1
    wcel
    nosgnn0i.1
    c0
    cX
    @1
    eleq1
    mpbiri
    mto
    neir
end
