include "wn.mm"
include "wo.mm"
include "wt.mm"
include "wf.mm"
include "ax-a2.mm"
include "or0.mm"
include "ax-r1.mm"
include "ax-r4.mm"
include "df-f.mm"
include "ax-r2.mm"
include "ax-r5.mm"
include "3tr1.mm"

theorem skr0
  param wva: term a
  param wvb: term b
  assume skr0.1: |- a = 1
  assume skr0.2: |- ( a ' v b ) = 1


  assert |- b = 1

  proof
    wvb
    wva
    wn
    #
    wvb
    wo
    #
    wt
    wvb
    wf
    wo
    #
    wf
    wvb
    wo
    wvb
    @1
    wvb
    wf
    ax-a2
    @2
    wvb
    wvb
    or0
    ax-r1
    @0
    wf
    wvb
    @0
    wt
    wn
    #
    wf
    wva
    wt
    skr0.1
    ax-r4
    wf
    @3
    df-f
    ax-r1
    ax-r2
    ax-r5
    3tr1
    skr0.2
    ax-r2
end
