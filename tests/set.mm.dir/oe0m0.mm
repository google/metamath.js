include "c0.mm"
include "con0.mm"
include "wcel.mm"
include "coe.mm"
include "co.mm"
include "c1o.mm"
include "wceq.mm"
include "0elon.mm"
include "cdif.mm"
include "oe0m.mm"
include "dif0.mm"
include "syl6eq.mm"
include "ax-mp.mm"

theorem oe0m0



  assert |- ( (/) ^o (/) ) = 1o

  proof
    c0
    con0
    wcel
    #
    c0
    c0
    coe
    co
    #
    c1o
    wceq
    0elon
    @0
    @1
    c1o
    c0
    cdif
    c1o
    c0
    oe0m
    c1o
    dif0
    syl6eq
    ax-mp
end
