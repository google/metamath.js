include "cv.mm"
include "cc0.mm"
include "wceq.mm"
include "cn.mm"
include "wcel.mm"
include "cneg.mm"
include "w3o.mm"
include "cr.mm"
include "cz.mm"
include "eqeq1.mm"
include "eleq1.mm"
include "negeq.mm"
include "eleq1d.mm"
include "3orbi123d.mm"
include "df-z.mm"
include "elrab2.mm"

theorem elz
  let cN: class N
  let vx: setvar x


  assert |- ( N e. ZZ <-> ( N e. RR /\ ( N = 0 \/ N e. NN \/ -u N e. NN ) ) )

  proof
    vx
    cv
    #
    cc0
    wceq
    #
    @0
    cn
    wcel
    #
    @0
    cneg
    #
    cn
    wcel
    #
    w3o
    cN
    cc0
    wceq
    #
    cN
    cn
    wcel
    #
    cN
    cneg
    #
    cn
    wcel
    #
    w3o
    vx
    cN
    cr
    cz
    @0
    cN
    wceq
    #
    @1
    @5
    @2
    @6
    @4
    @8
    @0
    cN
    cc0
    eqeq1
    @0
    cN
    cn
    eleq1
    @9
    @3
    @7
    cn
    @0
    cN
    negeq
    eleq1d
    3orbi123d
    vx
    df-z
    elrab2
end
