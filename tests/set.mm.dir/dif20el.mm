include "con0.mm"
include "c2o.mm"
include "cdif.mm"
include "wcel.mm"
include "c1o.mm"
include "c0.mm"
include "ondif2.mm"
include "simprbi.mm"
include "0lt1o.mm"
include "wa.mm"
include "wi.mm"
include "eldifi.mm"
include "ontr1.mm"
include "syl.mm"
include "mpani.mm"
include "mpd.mm"

theorem dif20el
  let cA: class A


  assert |- ( A e. ( On \ 2o ) -> (/) e. A )

  proof
    cA
    con0
    c2o
    cdif
    wcel
    #
    c1o
    cA
    wcel
    #
    c0
    cA
    wcel
    #
    @0
    cA
    con0
    wcel
    #
    @1
    cA
    ondif2
    simprbi
    @0
    c0
    c1o
    wcel
    #
    @1
    @2
    0lt1o
    @0
    @3
    @4
    @1
    wa
    @2
    wi
    cA
    con0
    c2o
    eldifi
    c0
    c1o
    cA
    ontr1
    syl
    mpani
    mpd
end
