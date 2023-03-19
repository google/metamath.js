include "wn.mm"
include "wi1.mm"
include "wo.mm"
include "leo.mm"
include "wa.mm"
include "wt.mm"
include "i1orni1.mm"
include "lan.mm"
include "ax-r1.mm"
include "an1.mm"
include "u1lemc6.mm"
include "negantlem1.mm"
include "comcom.mm"
include "fh4rc.mm"
include "3tr1.mm"
include "ancom.mm"
include "u1lemaa.mm"
include "3tr2.mm"
include "lear.mm"
include "bltr.mm"
include "ler2an.mm"
include "lea.mm"
include "ax-a1.mm"
include "lbtr.mm"
include "leror.mm"
include "u1lemab.mm"
include "ax-r2.mm"
include "df-i1.mm"
include "le3tr1.mm"
include "letr.mm"
include "leid.mm"
include "lel2or.mm"

theorem negantlem2
  param wva: term a
  param wvb: term b
  param wvc: term c
  assume negant.1: |- ( a ->1 c ) = ( b ->1 c )


  assert |- a =< ( b ' ->1 c )

  proof
    wva
    wva
    wvb
    wn
    #
    wvc
    wi1
    #
    wo
    #
    @1
    wva
    @1
    leo
    @2
    wva
    wvb
    wvc
    wi1
    #
    wa
    #
    @1
    wo
    #
    @1
    @2
    wt
    wa
    #
    @2
    @3
    @1
    wo
    #
    wa
    #
    @2
    @5
    @8
    @6
    @7
    wt
    @2
    wvb
    wvc
    i1orni1
    lan
    ax-r1
    @6
    @2
    @2
    an1
    ax-r1
    @3
    @1
    wva
    wvb
    wvc
    u1lemc6
    wva
    @3
    wva
    wvb
    wvc
    negant.1
    negantlem1
    comcom
    fh4rc
    3tr1
    @4
    @1
    @1
    @4
    wvc
    @3
    wa
    #
    @1
    @4
    wvc
    @3
    @4
    wva
    wvc
    wa
    #
    wvc
    wva
    wva
    wvc
    wi1
    #
    wa
    @11
    wva
    wa
    @4
    @10
    wva
    @11
    ancom
    @11
    @3
    wva
    negant.1
    lan
    wva
    wvc
    u1lemaa
    3tr2
    wva
    wvc
    lear
    bltr
    wva
    @3
    lear
    ler2an
    wvb
    wvc
    wa
    #
    @0
    wvc
    wa
    #
    wo
    #
    @0
    wn
    #
    @13
    wo
    @9
    @1
    @12
    @15
    @13
    @12
    wvb
    @15
    wvb
    wvc
    lea
    wvb
    ax-a1
    lbtr
    leror
    @9
    @3
    wvc
    wa
    @14
    wvc
    @3
    ancom
    wvb
    wvc
    u1lemab
    ax-r2
    @0
    wvc
    df-i1
    le3tr1
    letr
    @1
    leid
    lel2or
    bltr
    letr
end
