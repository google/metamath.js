include "cnr.mm"
include "cv.mm"
include "c1.mm"
include "co.mm"
include "c0.mm"
include "wbr.mm"
include "cc0.mm"
include "wcel.mm"
include "cop.mm"
include "noel.mm"
include "df-br.mm"
include "mtbir.mm"
include "intnan.mm"

theorem helloworld
  let vh: setvar h
  let cL: class L
  let cW: class W
  let vd: setvar d


  assert |- -. ( h e. ( L L 0 ) /\ W (/) ( R. 1 d ) )

  proof
    cW
    cnr
    vd
    cv
    c1
    co
    #
    c0
    wbr
    #
    vh
    cv
    cL
    cc0
    cL
    co
    wcel
    @1
    cW
    @0
    cop
    #
    c0
    wcel
    @2
    noel
    cW
    @0
    c0
    df-br
    mtbir
    intnan
end
