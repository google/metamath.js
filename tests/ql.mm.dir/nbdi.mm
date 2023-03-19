include "tb.mm"
include "wn.mm"
include "wo.mm"
include "wa.mm"
include "dfnb.mm"
include "comorr.mm"
include "comcom.mm"
include "comcom2.mm"
include "ax-a2.mm"
include "cbtr.mm"
include "fh1.mm"
include "ax-r2.mm"

theorem nbdi
  let wva: term a
  let wvb: term b


  assert |- ( a == b ) ' = ( ( ( a v b ) ^ a ' ) v ( ( a v b ) ^ b ' ) )

  proof
    wva
    wvb
    tb
    wn
    wva
    wvb
    wo
    #
    wva
    wn
    #
    wvb
    wn
    #
    wo
    wa
    @0
    @1
    wa
    @0
    @2
    wa
    wo
    wva
    wvb
    dfnb
    @0
    @1
    @2
    @0
    wva
    wva
    @0
    wva
    wvb
    comorr
    comcom
    comcom2
    @0
    wvb
    wvb
    @0
    wvb
    wvb
    wva
    wo
    @0
    wvb
    wva
    comorr
    wvb
    wva
    ax-a2
    cbtr
    comcom
    comcom2
    fh1
    ax-r2
end
