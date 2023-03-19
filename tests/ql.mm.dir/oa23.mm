include "wi2.mm"
include "wo.mm"
include "wn.mm"
include "wa.mm"
include "ax-a2.mm"
include "ax-r4.mm"
include "ancom.mm"
include "2or.mm"
include "lan.mm"
include "ax-r5.mm"
include "wt.mm"
include "ax-a3.mm"
include "ax-r1.mm"
include "oridm.mm"
include "ax-r2.mm"
include "u2lemonb.mm"
include "2an.mm"
include "an1.mm"
include "comorr.mm"
include "u2lemc1.mm"
include "comcom.mm"
include "comcom2.mm"
include "fh3.mm"
include "3tr1.mm"
include "lea.mm"
include "ler2an.mm"
include "u2lemanb.mm"
include "le3tr1.mm"
include "lelor.mm"
include "orabs.mm"
include "lbtr.mm"
include "bltr.mm"
include "leo.mm"
include "lebi.mm"
include "3tr.mm"
include "df-le1.mm"

theorem oa23
  let wva: term a
  let wvb: term b
  let wvc: term c
  assume oa23.1: |- ( c ' ^ ( ( a ->2 c ) v ( ( a ->2 b ) ^ ( ( c v b ) ' v ( ( a ->2 c ) ^ ( a ->2 b ) ) ) ) ) ) =< a '


  assert |- ( ( a ->2 b ) ^ ( ( b v c ) ' v ( ( a ->2 b ) ^ ( a ->2 c ) ) ) ) =< ( a ->2 c )

  proof
    wva
    wvb
    wi2
    #
    wvb
    wvc
    wo
    #
    wn
    #
    @0
    wva
    wvc
    wi2
    #
    wa
    #
    wo
    #
    wa
    #
    @3
    @6
    @3
    wo
    @0
    wvc
    wvb
    wo
    #
    wn
    #
    @3
    @0
    wa
    #
    wo
    #
    wa
    #
    @3
    wo
    @3
    @11
    wo
    #
    @3
    @6
    @11
    @3
    @5
    @10
    @0
    @2
    @8
    @4
    @9
    @1
    @7
    wvb
    wvc
    ax-a2
    ax-r4
    @0
    @3
    ancom
    2or
    lan
    ax-r5
    @11
    @3
    ax-a2
    @12
    @3
    @12
    @3
    @12
    wvc
    wn
    #
    wa
    #
    wo
    #
    @3
    @12
    wt
    wa
    #
    @3
    @12
    wo
    #
    @3
    @13
    wo
    #
    wa
    #
    @12
    @15
    @19
    @16
    @17
    @12
    @18
    wt
    @17
    @3
    @3
    wo
    #
    @11
    wo
    #
    @12
    @21
    @17
    @3
    @3
    @11
    ax-a3
    ax-r1
    @20
    @3
    @11
    @3
    oridm
    ax-r5
    ax-r2
    wva
    wvc
    u2lemonb
    2an
    ax-r1
    @16
    @12
    @12
    an1
    ax-r1
    @3
    @12
    @13
    @3
    @11
    comorr
    @3
    wvc
    wvc
    @3
    wva
    wvc
    u2lemc1
    comcom
    comcom2
    fh3
    3tr1
    @15
    @3
    @3
    @13
    wa
    #
    wo
    @3
    @14
    @22
    @3
    @13
    @12
    wa
    #
    wva
    wn
    #
    @13
    wa
    @14
    @22
    @23
    @24
    @13
    oa23.1
    @13
    @12
    lea
    ler2an
    @12
    @13
    ancom
    wva
    wvc
    u2lemanb
    le3tr1
    lelor
    @3
    @13
    orabs
    lbtr
    bltr
    @3
    @11
    leo
    lebi
    3tr
    df-le1
end
