include "wo.mm"
include "wa.mm"
include "ax-a2.mm"
include "ax-r1.mm"
include "ancom.mm"
include "ax-r2.mm"
include "lor.mm"
include "orabs.mm"

theorem leao
  param wva: term a
  param wvb: term b
  param wvc: term c
  assume leao.1: |- ( c ^ b ) = a


  assert |- ( a v b ) = b

  proof
    wva
    wvb
    wo
    #
    wvb
    wvb
    wvc
    wa
    #
    wo
    #
    wvb
    @0
    wvb
    wva
    wo
    @2
    wva
    wvb
    ax-a2
    wva
    @1
    wvb
    wva
    wvc
    wvb
    wa
    #
    @1
    @3
    wva
    leao.1
    ax-r1
    @1
    @3
    wvb
    wvc
    ancom
    ax-r1
    ax-r2
    lor
    ax-r2
    wvb
    wvc
    orabs
    ax-r2
end
