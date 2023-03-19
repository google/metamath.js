include "wo.mm"
include "wn.mm"
include "wi1.mm"
include "wa.mm"
include "lear.mm"
include "bltr.mm"
include "lecon.mm"
include "ax-r4.mm"
include "le3tr1.mm"

theorem gomaex3h4
  param wvc: term c
  param wvd: term d
  param wvj: term j
  param wvk: term k
  param wvp: term p
  param wvq: term q
  param wvr: term r
  assume gomaex3h4.11: |- r = ( ( p ' ->1 q ) ' ^ ( c v d ) )
  assume gomaex3h4.15: |- j = ( c v d ) '
  assume gomaex3h4.16: |- k = r


  assert |- j =< k '

  proof
    wvc
    wvd
    wo
    #
    wn
    wvr
    wn
    wvj
    wvk
    wn
    wvr
    @0
    wvr
    wvp
    wn
    wvq
    wi1
    wn
    #
    @0
    wa
    @0
    gomaex3h4.11
    @1
    @0
    lear
    bltr
    lecon
    gomaex3h4.15
    wvk
    wvr
    gomaex3h4.16
    ax-r4
    le3tr1
end
