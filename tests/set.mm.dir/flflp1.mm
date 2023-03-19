include "cr.mm"
include "wcel.mm"
include "wa.mm"
include "cfl.mm"
include "cfv.mm"
include "cle.mm"
include "wbr.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "clt.mm"
include "flltp1.mm"
include "ad3antrrr.mm"
include "cv.mm"
include "cz.mm"
include "crio.mm"
include "wceq.mm"
include "flval.mm"
include "ad3antlr.mm"
include "simplr.mm"
include "adantr.mm"
include "wi.mm"
include "reflcl.mm"
include "peano2re.mm"
include "syl.mm"
include "adantl.mm"
include "lttr.mm"
include "mpd3an3.mm"
include "ancoms.mm"
include "mpan2d.mm"
include "imp.mm"
include "adantlr.mm"
include "wb.mm"
include "wreu.mm"
include "flcl.mm"
include "rebtwnz.mm"
include "breq1.mm"
include "oveq1.mm"
include "breq2d.mm"
include "anbi12d.mm"
include "riota2.mm"
include "syl2an.mm"
include "ad2antrr.mm"
include "mpbi2and.mm"
include "eqtrd.mm"
include "oveq1d.mm"
include "breqtrrd.mm"
include "ex.mm"
include "wn.mm"
include "lenlt.mm"
include "lelttr.mm"
include "sylbird.mm"
include "pm2.61d.mm"
include "ad2antlr.mm"
include "simpll.mm"
include "flle.mm"
include "simpr.mm"
include "lelttrd.mm"
include "ltled.mm"
include "syl2anr.mm"
include "eqbrtrd.mm"
include "letr.mm"
include "3coml.mm"
include "mpand.mm"
include "impbida.mm"

theorem flflp1
  let cA: class A
  let cB: class B
  let vx: setvar x


  assert |- ( ( A e. RR /\ B e. RR ) -> ( ( |_ ` A ) <_ B <-> A < ( ( |_ ` B ) + 1 ) ) )

  proof
    cA
    cr
    wcel
    #
    cB
    cr
    wcel
    #
    wa
    #
    cA
    cfl
    cfv
    #
    cB
    cle
    wbr
    #
    cA
    cB
    cfl
    cfv
    #
    c1
    caddc
    co
    #
    clt
    wbr
    #
    @2
    @4
    wa
    #
    cB
    cA
    clt
    wbr
    #
    @7
    @8
    @9
    @7
    @8
    @9
    wa
    #
    cA
    @3
    c1
    caddc
    co
    #
    @6
    clt
    @0
    cA
    @11
    clt
    wbr
    #
    @1
    @4
    @9
    cA
    flltp1
    #
    ad3antrrr
    @10
    @5
    @3
    c1
    caddc
    @10
    @5
    vx
    cv
    #
    cB
    cle
    wbr
    #
    cB
    @14
    c1
    caddc
    co
    #
    clt
    wbr
    #
    wa
    #
    vx
    cz
    crio
    #
    @3
    @1
    @5
    @19
    wceq
    @0
    @4
    @9
    vx
    cB
    flval
    ad3antlr
    @10
    @4
    cB
    @11
    clt
    wbr
    #
    @19
    @3
    wceq
    #
    @2
    @4
    @9
    simplr
    @2
    @9
    @20
    @4
    @2
    @9
    @20
    @2
    @9
    @12
    @20
    @0
    @12
    @1
    @13
    adantr
    @1
    @0
    @9
    @12
    wa
    @20
    wi
    #
    @1
    @0
    @11
    cr
    wcel
    #
    @22
    @0
    @23
    @1
    @0
    @3
    cr
    wcel
    #
    @23
    cA
    reflcl
    #
    @3
    peano2re
    syl
    adantl
    cB
    cA
    @11
    lttr
    mpd3an3
    ancoms
    mpan2d
    imp
    adantlr
    @2
    @4
    @20
    wa
    #
    @21
    wb
    #
    @4
    @9
    @0
    @3
    cz
    wcel
    @18
    vx
    cz
    wreu
    @27
    @1
    cA
    flcl
    vx
    cB
    rebtwnz
    @18
    @26
    vx
    cz
    @3
    @14
    @3
    wceq
    #
    @15
    @4
    @17
    @20
    @14
    @3
    cB
    cle
    breq1
    @28
    @16
    @11
    cB
    clt
    @14
    @3
    c1
    caddc
    oveq1
    breq2d
    anbi12d
    riota2
    syl2an
    ad2antrr
    mpbi2and
    eqtrd
    oveq1d
    breqtrrd
    ex
    @2
    @9
    wn
    #
    @7
    wi
    @4
    @2
    @29
    cA
    cB
    cle
    wbr
    #
    @7
    cA
    cB
    lenlt
    #
    @2
    @30
    cB
    @6
    clt
    wbr
    #
    @7
    @1
    @32
    @0
    cB
    flltp1
    adantl
    @0
    @1
    @6
    cr
    wcel
    #
    @30
    @32
    wa
    @7
    wi
    @1
    @33
    @0
    @1
    @5
    cr
    wcel
    #
    @33
    cB
    reflcl
    #
    @5
    peano2re
    syl
    adantl
    cA
    cB
    @6
    lelttr
    mpd3an3
    mpan2d
    sylbird
    adantr
    pm2.61d
    @2
    @7
    wa
    #
    @9
    @4
    @36
    @9
    @4
    @36
    @9
    wa
    #
    @3
    @5
    cB
    cle
    @37
    @3
    @14
    cA
    cle
    wbr
    #
    cA
    @16
    clt
    wbr
    #
    wa
    #
    vx
    cz
    crio
    #
    @5
    @0
    @3
    @41
    wceq
    @1
    @7
    @9
    vx
    cA
    flval
    ad3antrrr
    @37
    @5
    cA
    cle
    wbr
    #
    @7
    @41
    @5
    wceq
    #
    @2
    @9
    @42
    @7
    @2
    @9
    wa
    #
    @5
    cA
    @1
    @34
    @0
    @9
    @35
    ad2antlr
    #
    @0
    @1
    @9
    simpll
    #
    @44
    @5
    cB
    cA
    @45
    @0
    @1
    @9
    simplr
    @46
    @1
    @5
    cB
    cle
    wbr
    #
    @0
    @9
    cB
    flle
    #
    ad2antlr
    @2
    @9
    simpr
    lelttrd
    ltled
    adantlr
    @2
    @7
    @9
    simplr
    @2
    @42
    @7
    wa
    #
    @43
    wb
    #
    @7
    @9
    @1
    @5
    cz
    wcel
    @40
    vx
    cz
    wreu
    @50
    @0
    cB
    flcl
    vx
    cA
    rebtwnz
    @40
    @49
    vx
    cz
    @5
    @14
    @5
    wceq
    #
    @38
    @42
    @39
    @7
    @14
    @5
    cA
    cle
    breq1
    @51
    @16
    @6
    cA
    clt
    @14
    @5
    c1
    caddc
    oveq1
    breq2d
    anbi12d
    riota2
    syl2anr
    ad2antrr
    mpbi2and
    eqtrd
    @1
    @47
    @0
    @7
    @9
    @48
    ad3antlr
    eqbrtrd
    ex
    @2
    @29
    @4
    wi
    @7
    @2
    @29
    @30
    @4
    @31
    @2
    @3
    cA
    cle
    wbr
    #
    @30
    @4
    @0
    @52
    @1
    cA
    flle
    adantr
    @0
    @1
    @24
    @52
    @30
    wa
    @4
    wi
    #
    @0
    @24
    @1
    @25
    adantr
    @24
    @0
    @1
    @53
    @3
    cA
    cB
    letr
    3coml
    mpd3an3
    mpand
    sylbird
    adantr
    pm2.61d
    impbida
end
