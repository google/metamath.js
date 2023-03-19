include "wa.mm"
include "wn.mm"
include "wo.mm"
include "wi4.mm"
include "leao4.mm"
include "wi1.mm"
include "leor.mm"
include "df-i1.mm"
include "ax-r1.mm"
include "lbtr.mm"
include "lear.mm"
include "ler2an.mm"
include "ran.mm"
include "u1lemab.mm"
include "ancom.mm"
include "2or.mm"
include "ax-a2.mm"
include "ax-r2.mm"
include "lor.mm"
include "ax-a3.mm"
include "bltr.mm"
include "letr.mm"
include "negant.mm"
include "ax-a1.mm"
include "lel2or.mm"
include "lea.mm"
include "negantlem8.mm"
include "leao2.mm"
include "ler.mm"
include "df-i4.mm"
include "dfi4b.mm"
include "le3tr1.mm"

theorem negantlem10
  param wva: term a
  param wvb: term b
  param wvc: term c
  assume negant.1: |- ( a ->1 c ) = ( b ->1 c )


  assert |- ( a ->4 c ) =< ( b ->4 c )

  proof
    wva
    wvc
    wa
    #
    wva
    wn
    #
    wvc
    wa
    #
    wo
    #
    @1
    wvc
    wo
    #
    wvc
    wn
    #
    wa
    #
    wo
    wvb
    wn
    #
    wvc
    wo
    #
    @5
    wvc
    @7
    wa
    #
    wo
    #
    wvc
    wvb
    wa
    #
    wo
    #
    wa
    #
    wva
    wvc
    wi4
    wvb
    wvc
    wi4
    @3
    @13
    @6
    @0
    @13
    @2
    @0
    @8
    @12
    wvc
    wva
    @7
    leao4
    @0
    wva
    wvc
    wi1
    #
    wvc
    wa
    #
    @12
    @0
    @14
    wvc
    @0
    @1
    @0
    wo
    #
    @14
    @0
    @1
    leor
    @14
    @16
    wva
    wvc
    df-i1
    ax-r1
    lbtr
    wva
    wvc
    lear
    ler2an
    @15
    wvb
    wvc
    wi1
    #
    wvc
    wa
    #
    @12
    @14
    @17
    wvc
    negant.1
    ran
    @18
    wvb
    wvc
    wa
    #
    @7
    wvc
    wa
    #
    wo
    #
    @12
    wvb
    wvc
    u1lemab
    @21
    @5
    @21
    wo
    #
    @12
    @21
    @5
    leor
    @22
    @5
    @9
    @11
    wo
    #
    wo
    #
    @12
    @21
    @23
    @5
    @21
    @11
    @9
    wo
    @23
    @19
    @11
    @20
    @9
    wvb
    wvc
    ancom
    @7
    wvc
    ancom
    2or
    @11
    @9
    ax-a2
    ax-r2
    lor
    @12
    @24
    @5
    @9
    @11
    ax-a3
    ax-r1
    #
    ax-r2
    lbtr
    bltr
    bltr
    letr
    ler2an
    @2
    @8
    @12
    wvc
    @1
    @7
    leao4
    @2
    @1
    wvc
    wi1
    #
    wvc
    wa
    #
    @12
    @2
    @26
    wvc
    @2
    @1
    wn
    #
    @2
    wo
    #
    @26
    @2
    @28
    leor
    @26
    @29
    @1
    wvc
    df-i1
    ax-r1
    lbtr
    @1
    wvc
    lear
    ler2an
    @27
    @7
    wvc
    wi1
    #
    wvc
    wa
    #
    @12
    @26
    @30
    wvc
    wva
    wvb
    wvc
    negant.1
    negant
    ran
    @31
    @20
    @7
    wn
    #
    wvc
    wa
    #
    wo
    #
    @12
    @7
    wvc
    u1lemab
    @34
    @5
    @34
    wo
    #
    @12
    @34
    @5
    leor
    @35
    @24
    @12
    @24
    @35
    @23
    @34
    @5
    @9
    @20
    @11
    @33
    wvc
    @7
    ancom
    @11
    @19
    @33
    wvc
    wvb
    ancom
    wvb
    @32
    wvc
    wvb
    ax-a1
    ran
    ax-r2
    2or
    lor
    ax-r1
    @25
    ax-r2
    lbtr
    bltr
    bltr
    letr
    ler2an
    lel2or
    @6
    @8
    @12
    @6
    @4
    @8
    @4
    @5
    lea
    wva
    wvb
    wvc
    negant.1
    negantlem8
    lbtr
    @6
    @10
    @11
    @5
    @4
    @9
    leao2
    ler
    ler2an
    lel2or
    wva
    wvc
    df-i4
    wvb
    wvc
    dfi4b
    le3tr1
end
