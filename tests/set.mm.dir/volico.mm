include "cr.mm"
include "wcel.mm"
include "wa.mm"
include "clt.mm"
include "wbr.mm"
include "cico.mm"
include "co.mm"
include "cvol.mm"
include "cfv.mm"
include "cmin.mm"
include "cc0.mm"
include "cif.mm"
include "wceq.mm"
include "w3a.mm"
include "cioo.mm"
include "csn.mm"
include "cun.mm"
include "caddc.mm"
include "cxr.mm"
include "rexr.mm"
include "3ad2ant1.mm"
include "3ad2ant2.mm"
include "simp3.mm"
include "snunioo1.mm"
include "syl3anc.mm"
include "eqcomd.mm"
include "fveq2d.mm"
include "cdm.mm"
include "cin.mm"
include "c0.mm"
include "ioombl.mm"
include "a1i.mm"
include "snmbl.mm"
include "wn.mm"
include "lbioo.mm"
include "disjsn.mm"
include "mpbir.mm"
include "ioovolcl.mm"
include "3adant3.mm"
include "volsn.mm"
include "0red.mm"
include "eqeltrd.mm"
include "volun.mm"
include "syl32anc.mm"
include "cle.mm"
include "simp1.mm"
include "simp2.mm"
include "ltled.mm"
include "volioo.mm"
include "oveq12d.mm"
include "recnd.mm"
include "cc.mm"
include "recn.mm"
include "subcld.mm"
include "addid1d.mm"
include "eqtrd.mm"
include "3eqtrd.mm"
include "3expa.mm"
include "iftrue.mm"
include "adantl.mm"
include "eqtr4d.mm"
include "simpl.mm"
include "simpr.mm"
include "simprd.mm"
include "simpld.mm"
include "lenltd.mm"
include "mpbird.mm"
include "wb.mm"
include "ad2antrr.mm"
include "ad2antlr.mm"
include "ico0.mm"
include "syl2anc.mm"
include "vol0.mm"
include "iffalse.mm"
include "pm2.61dan.mm"

theorem volico
  let cA: class A
  let cB: class B
  let vk: setvar k
  let vx: setvar x


  assert |- ( ( A e. RR /\ B e. RR ) -> ( vol ` ( A [,) B ) ) = if ( A < B , ( B - A ) , 0 ) )

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
    clt
    wbr
    #
    cA
    cB
    cico
    co
    #
    cvol
    cfv
    #
    @3
    cB
    cA
    cmin
    co
    #
    cc0
    cif
    #
    wceq
    @2
    @3
    wa
    @5
    @6
    @7
    @0
    @1
    @3
    @5
    @6
    wceq
    @0
    @1
    @3
    w3a
    #
    @5
    cA
    cB
    cioo
    co
    #
    cA
    csn
    #
    cun
    #
    cvol
    cfv
    #
    @9
    cvol
    cfv
    #
    @10
    cvol
    cfv
    #
    caddc
    co
    #
    @6
    @8
    @4
    @11
    cvol
    @8
    @11
    @4
    @8
    cA
    cxr
    wcel
    #
    cB
    cxr
    wcel
    #
    @3
    @11
    @4
    wceq
    @0
    @1
    @16
    @3
    cA
    rexr
    #
    3ad2ant1
    @1
    @0
    @17
    @3
    cB
    rexr
    #
    3ad2ant2
    @0
    @1
    @3
    simp3
    #
    cA
    cB
    snunioo1
    syl3anc
    eqcomd
    fveq2d
    @8
    @9
    cvol
    cdm
    #
    wcel
    #
    @10
    @21
    wcel
    #
    @9
    @10
    cin
    c0
    wceq
    #
    @13
    cr
    wcel
    #
    @14
    cr
    wcel
    #
    @12
    @15
    wceq
    @22
    @8
    cA
    cB
    ioombl
    a1i
    @0
    @1
    @23
    @3
    cA
    snmbl
    3ad2ant1
    @24
    @8
    @24
    cA
    @9
    wcel
    wn
    cA
    cB
    lbioo
    @9
    cA
    disjsn
    mpbir
    a1i
    @0
    @1
    @25
    @3
    cA
    cB
    ioovolcl
    3adant3
    @0
    @1
    @26
    @3
    @0
    @14
    cc0
    cr
    cA
    volsn
    #
    @0
    0red
    eqeltrd
    3ad2ant1
    @9
    @10
    volun
    syl32anc
    @8
    @15
    @6
    cc0
    caddc
    co
    @6
    @8
    @13
    @6
    @14
    cc0
    caddc
    @8
    @0
    @1
    cA
    cB
    cle
    wbr
    @13
    @6
    wceq
    @0
    @1
    @3
    simp1
    #
    @0
    @1
    @3
    simp2
    #
    @8
    cA
    cB
    @28
    @29
    @20
    ltled
    cA
    cB
    volioo
    syl3anc
    @0
    @1
    @14
    cc0
    wceq
    @3
    @27
    3ad2ant1
    oveq12d
    @8
    @6
    @8
    cB
    cA
    @8
    cB
    @29
    recnd
    @0
    @1
    cA
    cc
    wcel
    @3
    cA
    recn
    3ad2ant1
    subcld
    addid1d
    eqtrd
    3eqtrd
    3expa
    @3
    @7
    @6
    wceq
    @2
    @3
    @6
    cc0
    iftrue
    adantl
    eqtr4d
    @2
    @3
    wn
    #
    wa
    #
    @5
    cc0
    @7
    @31
    @2
    cB
    cA
    cle
    wbr
    #
    @5
    cc0
    wceq
    @2
    @30
    simpl
    #
    @31
    @32
    @30
    @2
    @30
    simpr
    @31
    cB
    cA
    @31
    @0
    @1
    @33
    simprd
    @31
    @0
    @1
    @33
    simpld
    lenltd
    mpbird
    @2
    @32
    wa
    #
    @5
    c0
    cvol
    cfv
    #
    cc0
    @34
    @4
    c0
    cvol
    @34
    @4
    c0
    wceq
    #
    @32
    @2
    @32
    simpr
    @34
    @16
    @17
    @36
    @32
    wb
    @0
    @16
    @1
    @32
    @18
    ad2antrr
    @1
    @17
    @0
    @32
    @19
    ad2antlr
    cA
    cB
    ico0
    syl2anc
    mpbird
    fveq2d
    @35
    cc0
    wceq
    @34
    vol0
    a1i
    eqtrd
    syl2anc
    @30
    @7
    cc0
    wceq
    @2
    @3
    @6
    cc0
    iffalse
    adantl
    eqtr4d
    pm2.61dan
end
