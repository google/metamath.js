include "cr.mm"
include "wcel.mm"
include "wa.mm"
include "cle.mm"
include "wbr.mm"
include "cif.mm"
include "caddc.mm"
include "co.mm"
include "cmin.mm"
include "cabs.mm"
include "cfv.mm"
include "c2.mm"
include "cdiv.mm"
include "wceq.mm"
include "clt.mm"
include "cmul.mm"
include "cc.mm"
include "recn.mm"
include "cc0.mm"
include "wne.mm"
include "2cn.mm"
include "2ne0.mm"
include "divcan3.mm"
include "mp3an23.mm"
include "syl.mm"
include "ad2antlr.mm"
include "ltle.mm"
include "imp.mm"
include "abssubge0.mm"
include "3expa.mm"
include "syldan.mm"
include "oveq2d.mm"
include "simpr.mm"
include "simpl.mm"
include "ppncand.mm"
include "2times.mm"
include "adantl.mm"
include "eqtr4d.mm"
include "syl2an.mm"
include "adantr.mm"
include "eqtrd.mm"
include "oveq1d.mm"
include "wn.mm"
include "ltnle.mm"
include "biimpa.mm"
include "iffalsed.mm"
include "3eqtr4rd.mm"
include "ancom1s.mm"
include "abssuble0.mm"
include "addcom.mm"
include "3eqtr4d.mm"
include "iftrue.mm"
include "ltlecasei.mm"

theorem absmax
  let cA: class A
  let cB: class B


  assert |- ( ( A e. RR /\ B e. RR ) -> if ( A <_ B , B , A ) = ( ( ( A + B ) + ( abs ` ( A - B ) ) ) / 2 ) )

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
    cB
    cle
    wbr
    #
    cB
    cA
    cif
    #
    cA
    cB
    caddc
    co
    #
    cA
    cB
    cmin
    co
    #
    cabs
    cfv
    #
    caddc
    co
    #
    c2
    cdiv
    co
    #
    wceq
    #
    cB
    cA
    @1
    @0
    cB
    cA
    clt
    wbr
    #
    @10
    @1
    @0
    wa
    #
    @11
    wa
    #
    c2
    cA
    cmul
    co
    #
    c2
    cdiv
    co
    #
    cA
    @9
    @4
    @0
    @15
    cA
    wceq
    #
    @1
    @11
    @0
    cA
    cc
    wcel
    #
    @16
    cA
    recn
    #
    @17
    c2
    cc
    wcel
    #
    c2
    cc0
    wne
    #
    @16
    2cn
    2ne0
    cA
    c2
    divcan3
    mp3an23
    syl
    ad2antlr
    @13
    @8
    @14
    c2
    cdiv
    @13
    @8
    @5
    @6
    caddc
    co
    #
    @14
    @13
    @7
    @6
    @5
    caddc
    @12
    @11
    cB
    cA
    cle
    wbr
    #
    @7
    @6
    wceq
    #
    @12
    @11
    @22
    cB
    cA
    ltle
    imp
    @1
    @0
    @22
    @23
    cB
    cA
    abssubge0
    3expa
    syldan
    oveq2d
    @12
    @21
    @14
    wceq
    #
    @11
    @1
    cB
    cc
    wcel
    #
    @17
    @24
    @0
    cB
    recn
    #
    @18
    @25
    @17
    wa
    #
    @21
    cA
    cA
    caddc
    co
    #
    @14
    @27
    cA
    cB
    cA
    @25
    @17
    simpr
    #
    @25
    @17
    simpl
    @29
    ppncand
    @17
    @14
    @28
    wceq
    @25
    cA
    2times
    adantl
    eqtr4d
    syl2an
    adantr
    eqtrd
    oveq1d
    @13
    @3
    cB
    cA
    @12
    @11
    @3
    wn
    cB
    cA
    ltnle
    biimpa
    iffalsed
    3eqtr4rd
    ancom1s
    @2
    @3
    wa
    #
    c2
    cB
    cmul
    co
    #
    c2
    cdiv
    co
    #
    cB
    @9
    @4
    @1
    @32
    cB
    wceq
    #
    @0
    @3
    @1
    @25
    @33
    @26
    @25
    @19
    @20
    @33
    2cn
    2ne0
    cB
    c2
    divcan3
    mp3an23
    syl
    ad2antlr
    @30
    @8
    @31
    c2
    cdiv
    @30
    @8
    @5
    cB
    cA
    cmin
    co
    #
    caddc
    co
    #
    @31
    @30
    @7
    @34
    @5
    caddc
    @0
    @1
    @3
    @7
    @34
    wceq
    cA
    cB
    abssuble0
    3expa
    oveq2d
    @2
    @35
    @31
    wceq
    #
    @3
    @0
    @17
    @25
    @36
    @1
    @18
    @26
    @17
    @25
    wa
    #
    cB
    cA
    caddc
    co
    #
    @34
    caddc
    co
    cB
    cB
    caddc
    co
    #
    @35
    @31
    @37
    cB
    cA
    cB
    @17
    @25
    simpr
    #
    @17
    @25
    simpl
    @40
    ppncand
    @37
    @5
    @38
    @34
    caddc
    cA
    cB
    addcom
    oveq1d
    @25
    @31
    @39
    wceq
    @17
    cB
    2times
    adantl
    3eqtr4d
    syl2an
    adantr
    eqtrd
    oveq1d
    @3
    @4
    cB
    wceq
    @2
    @3
    cB
    cA
    iftrue
    adantl
    3eqtr4rd
    @0
    @1
    simpr
    @0
    @1
    simpl
    ltlecasei
end
