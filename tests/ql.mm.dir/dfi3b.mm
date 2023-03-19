include "wn.mm"
include "wa.mm"
include "wo.mm"
include "wi3.mm"
include "ax-a2.mm"
include "ax-a3.mm"
include "oridm.mm"
include "ax-r1.mm"
include "anidm.mm"
include "ran.mm"
include "anass.mm"
include "ax-r2.mm"
include "lan.mm"
include "an12.mm"
include "2or.mm"
include "lea.mm"
include "leo.mm"
include "letr.mm"
include "df2le2.mm"
include "ancom.mm"
include "comor1.mm"
include "comcom7.mm"
include "comor2.mm"
include "comcom2.mm"
include "com2an.mm"
include "fh1.mm"
include "coman1.mm"
include "coman2.mm"
include "fh1r.mm"
include "3tr1.mm"
include "df-i3.mm"
include "com2or.mm"

theorem dfi3b
  let wva: term a
  let wvb: term b


  assert |- ( a ->3 b ) = ( ( a ' v b ) ^ ( ( a v ( a ' ^ b ' ) ) v ( a ' ^ b ) ) )

  proof
    wva
    wn
    #
    wvb
    wa
    #
    @0
    wvb
    wn
    #
    wa
    #
    wo
    wva
    @0
    wvb
    wo
    #
    wa
    #
    wo
    #
    @4
    wva
    @3
    wo
    #
    wa
    #
    @4
    @1
    wa
    #
    wo
    #
    wva
    wvb
    wi3
    @4
    @7
    @1
    wo
    wa
    @0
    @1
    wa
    #
    wvb
    @1
    wa
    #
    wo
    #
    @4
    wva
    wa
    #
    @4
    @3
    wa
    #
    wo
    #
    wo
    #
    @16
    @13
    wo
    @6
    @10
    @13
    @16
    ax-a2
    @6
    @1
    @3
    @5
    wo
    #
    wo
    @17
    @1
    @3
    @5
    ax-a3
    @1
    @13
    @18
    @16
    @1
    @1
    @1
    wo
    #
    @13
    @19
    @1
    @1
    oridm
    ax-r1
    @1
    @11
    @1
    @12
    @1
    @0
    @0
    wa
    #
    wvb
    wa
    @11
    @0
    @20
    wvb
    @20
    @0
    @0
    anidm
    ax-r1
    ran
    @0
    @0
    wvb
    anass
    ax-r2
    @1
    @0
    wvb
    wvb
    wa
    #
    wa
    @12
    wvb
    @21
    @0
    @21
    wvb
    wvb
    anidm
    ax-r1
    lan
    @0
    wvb
    wvb
    an12
    ax-r2
    2or
    ax-r2
    @18
    @15
    @14
    wo
    @16
    @3
    @15
    @5
    @14
    @3
    @3
    @4
    wa
    #
    @15
    @22
    @3
    @3
    @4
    @3
    @0
    @4
    @0
    @2
    lea
    @0
    wvb
    leo
    letr
    df2le2
    ax-r1
    @3
    @4
    ancom
    ax-r2
    wva
    @4
    ancom
    2or
    @15
    @14
    ax-a2
    ax-r2
    2or
    ax-r2
    @8
    @16
    @9
    @13
    @4
    wva
    @3
    @4
    wva
    @0
    wvb
    comor1
    #
    comcom7
    #
    @4
    @0
    @2
    @23
    @4
    wvb
    @0
    wvb
    comor2
    #
    comcom2
    com2an
    #
    fh1
    @1
    @0
    wvb
    @0
    wvb
    coman1
    @0
    wvb
    coman2
    fh1r
    2or
    3tr1
    wva
    wvb
    df-i3
    @4
    @7
    @1
    @4
    wva
    @3
    @24
    @26
    com2or
    @4
    @0
    wvb
    @23
    @25
    com2an
    fh1
    3tr1
end
