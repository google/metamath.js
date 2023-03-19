include "wo.mm"
include "wi2.mm"
include "wa.mm"
include "wn.mm"
include "df-i2.mm"
include "lan.mm"
include "ax-a2.mm"
include "ran.mm"
include "lecom.mm"
include "comcom7.mm"
include "comcom.mm"
include "comcom2.mm"
include "com2an.mm"
include "com2or.mm"
include "fh2r.mm"
include "ax-r2.mm"
include "wf.mm"
include "coman1.mm"
include "coman2.mm"
include "fh2c.mm"
include "dff.mm"
include "ax-r1.mm"
include "anass.mm"
include "an0r.mm"
include "3tr2.mm"
include "lor.mm"
include "or0.mm"
include "3tr.mm"
include "lea.mm"
include "lear.mm"
include "le2or.mm"
include "bltr.mm"

theorem govar
  param wva: term a
  param wvb: term b
  param wvc: term c
  assume govar.1: |- a =< b '
  assume govar.2: |- b =< c '


  assert |- ( ( a v b ) ^ ( a ->2 c ) ) =< ( b v c )

  proof
    wva
    wvb
    wo
    #
    wva
    wvc
    wi2
    #
    wa
    #
    wvb
    wvc
    wva
    wn
    #
    wvc
    wn
    #
    wa
    #
    wo
    #
    wa
    #
    wva
    wvc
    wa
    #
    wo
    #
    wvb
    wvc
    wo
    @2
    @0
    @6
    wa
    #
    @7
    wva
    @6
    wa
    #
    wo
    #
    @9
    @1
    @6
    @0
    wva
    wvc
    df-i2
    lan
    @10
    wvb
    wva
    wo
    #
    @6
    wa
    @12
    @0
    @13
    @6
    wva
    wvb
    ax-a2
    ran
    wvb
    @6
    wva
    wvb
    wvc
    @5
    wvb
    wvc
    wvb
    @4
    govar.2
    lecom
    #
    comcom7
    wvb
    @3
    @4
    wvb
    wva
    wva
    wvb
    wva
    wvb
    wva
    wvb
    wn
    govar.1
    lecom
    comcom7
    comcom
    #
    comcom2
    @14
    com2an
    com2or
    @15
    fh2r
    ax-r2
    @11
    @8
    @7
    @11
    @8
    wva
    @5
    wa
    #
    wo
    @8
    wf
    wo
    @8
    @5
    wva
    wvc
    @5
    wva
    @3
    @4
    coman1
    comcom7
    @5
    wvc
    @3
    @4
    coman2
    comcom7
    fh2c
    @16
    wf
    @8
    wva
    @3
    wa
    #
    @4
    wa
    #
    wf
    @4
    wa
    #
    @16
    wf
    @19
    @18
    wf
    @17
    @4
    wva
    dff
    ran
    ax-r1
    wva
    @3
    @4
    anass
    @4
    an0r
    3tr2
    lor
    @8
    or0
    3tr
    lor
    3tr
    @7
    wvb
    @8
    wvc
    wvb
    @6
    lea
    wva
    wvc
    lear
    le2or
    bltr
end
