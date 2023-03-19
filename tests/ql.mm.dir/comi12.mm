include "wi1.mm"
include "wn.mm"
include "wa.mm"
include "wo.mm"
include "wi2.mm"
include "df-i1.mm"
include "lea.mm"
include "leo.mm"
include "letr.mm"
include "lecom.mm"
include "comcom.mm"
include "anor3.mm"
include "cbtr.mm"
include "comcom7.mm"
include "df-i2.mm"
include "ax-r1.mm"
include "bctr.mm"

theorem comi12
  param wva: term a
  param wvb: term b
  param wvc: term c


  assert |- ( a ->1 b ) C ( c ->2 a )

  proof
    wva
    wvb
    wi1
    wva
    wn
    #
    wva
    wvb
    wa
    #
    wo
    #
    wvc
    wva
    wi2
    #
    wva
    wvb
    df-i1
    @2
    wva
    wvc
    wn
    @0
    wa
    #
    wo
    #
    @3
    @2
    @5
    @2
    @0
    @4
    wn
    #
    wa
    #
    @5
    wn
    @7
    @2
    @7
    @2
    @7
    @0
    @2
    @0
    @6
    lea
    @0
    @1
    leo
    letr
    lecom
    comcom
    wva
    @4
    anor3
    cbtr
    comcom7
    @3
    @5
    wvc
    wva
    df-i2
    ax-r1
    cbtr
    bctr
end
