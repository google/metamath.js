include "wn.mm"
include "wi1.mm"
include "wo.mm"
include "wa.mm"
include "lea.mm"
include "bltr.mm"
include "ax-r4.mm"
include "le3tr1.mm"

theorem gomaex3h5
  param wvc: term c
  param wvd: term d
  param wvk: term k
  param wvm: term m
  param wvp: term p
  param wvq: term q
  param wvr: term r
  assume gomaex3h5.11: |- r = ( ( p ' ->1 q ) ' ^ ( c v d ) )
  assume gomaex3h5.16: |- k = r
  assume gomaex3h5.17: |- m = ( p ' ->1 q )


  assert |- k =< m '

  proof
    wvr
    wvp
    wn
    wvq
    wi1
    #
    wn
    #
    wvk
    wvm
    wn
    wvr
    @1
    wvc
    wvd
    wo
    #
    wa
    @1
    gomaex3h5.11
    @1
    @2
    lea
    bltr
    gomaex3h5.16
    wvm
    @0
    gomaex3h5.17
    ax-r4
    le3tr1
end
