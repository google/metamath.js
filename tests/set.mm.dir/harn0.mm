include "wcel.mm"
include "c0.mm"
include "char.mm"
include "cfv.mm"
include "wne.mm"
include "con0.mm"
include "cdom.mm"
include "wbr.mm"
include "0elon.mm"
include "a1i.mm"
include "0domg.mm"
include "elharval.mm"
include "sylanbrc.mm"
include "ne0i.mm"
include "syl.mm"

theorem harn0
  let cS: class S
  let cV: class V


  assert |- ( S e. V -> ( har ` S ) =/= (/) )

  proof
    cS
    cV
    wcel
    #
    c0
    cS
    char
    cfv
    #
    wcel
    #
    @1
    c0
    wne
    @0
    c0
    con0
    wcel
    #
    c0
    cS
    cdom
    wbr
    @2
    @3
    @0
    0elon
    a1i
    cS
    cV
    0domg
    cS
    c0
    elharval
    sylanbrc
    @1
    c0
    ne0i
    syl
end
