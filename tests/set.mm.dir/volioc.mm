include "cr.mm"
include "wcel.mm"
include "cle.mm"
include "wbr.mm"
include "w3a.mm"
include "wceq.mm"
include "cioc.mm"
include "co.mm"
include "cvol.mm"
include "cfv.mm"
include "cmin.mm"
include "wa.mm"
include "c0.mm"
include "cc0.mm"
include "vol0.mm"
include "oveq2.mm"
include "eqcomd.mm"
include "leid.mm"
include "cxr.mm"
include "wb.mm"
include "rexr.mm"
include "ioc0.mm"
include "syl2anc.mm"
include "mpbird.mm"
include "sylan9eqr.mm"
include "fveq2d.mm"
include "cc.mm"
include "eqcom.mm"
include "biimpi.mm"
include "adantl.mm"
include "recn.mm"
include "adantr.mm"
include "eqeltrd.mm"
include "subeq0bd.mm"
include "3eqtr4a.mm"
include "3ad2antl1.mm"
include "wn.mm"
include "clt.mm"
include "simpl1.mm"
include "simpl2.mm"
include "simpl3.mm"
include "wne.mm"
include "necon3bi.mm"
include "leneltd.mm"
include "cioo.mm"
include "csn.mm"
include "cun.mm"
include "caddc.mm"
include "3ad2ant1.mm"
include "3ad2ant2.mm"
include "simp3.mm"
include "snunioo2.mm"
include "syl3anc.mm"
include "cdm.mm"
include "cin.mm"
include "ioombl.mm"
include "a1i.mm"
include "snmbl.mm"
include "ubioo.mm"
include "disjsn.mm"
include "mpbir.mm"
include "ioovolcl.mm"
include "3adant3.mm"
include "volsn.mm"
include "0red.mm"
include "volun.mm"
include "syl32anc.mm"
include "simp1.mm"
include "simp2.mm"
include "ltled.mm"
include "volioo.mm"
include "oveq12d.mm"
include "recnd.mm"
include "subcld.mm"
include "addid1d.mm"
include "eqtrd.mm"
include "3eqtrd.mm"
include "pm2.61dan.mm"

theorem volioc
  let cA: class A
  let cB: class B
  let vk: setvar k
  let vx: setvar x


  assert |- ( ( A e. RR /\ B e. RR /\ A <_ B ) -> ( vol ` ( A (,] B ) ) = ( B - A ) )

  proof
    cA
    cr
    wcel
    #
    cB
    cr
    wcel
    #
    cA
    cB
    cle
    wbr
    #
    w3a
    #
    cA
    cB
    wceq
    #
    cA
    cB
    cioc
    co
    #
    cvol
    cfv
    #
    cB
    cA
    cmin
    co
    #
    wceq
    #
    @0
    @1
    @4
    @8
    @2
    @0
    @4
    wa
    #
    c0
    cvol
    cfv
    cc0
    @6
    @7
    vol0
    @9
    @5
    c0
    cvol
    @4
    @0
    @5
    cA
    cA
    cioc
    co
    #
    c0
    @4
    @10
    @5
    cA
    cB
    cA
    cioc
    oveq2
    eqcomd
    @0
    @10
    c0
    wceq
    #
    cA
    cA
    cle
    wbr
    #
    cA
    leid
    @0
    cA
    cxr
    wcel
    #
    @13
    @11
    @12
    wb
    cA
    rexr
    #
    @14
    cA
    cA
    ioc0
    syl2anc
    mpbird
    sylan9eqr
    fveq2d
    @9
    cB
    cA
    @9
    cB
    cA
    cc
    @4
    cB
    cA
    wceq
    #
    @0
    @4
    @15
    cA
    cB
    eqcom
    biimpi
    adantl
    #
    @0
    cA
    cc
    wcel
    #
    @4
    cA
    recn
    #
    adantr
    eqeltrd
    @16
    subeq0bd
    3eqtr4a
    3ad2antl1
    @3
    @4
    wn
    #
    wa
    #
    @0
    @1
    cA
    cB
    clt
    wbr
    #
    @8
    @0
    @1
    @2
    @19
    simpl1
    #
    @0
    @1
    @2
    @19
    simpl2
    #
    @20
    cA
    cB
    @22
    @23
    @0
    @1
    @2
    @19
    simpl3
    @19
    cB
    cA
    wne
    @3
    @4
    cB
    cA
    @15
    @4
    cB
    cA
    eqcom
    biimpi
    necon3bi
    adantl
    leneltd
    @0
    @1
    @21
    w3a
    #
    @6
    cA
    cB
    cioo
    co
    #
    cB
    csn
    #
    cun
    #
    cvol
    cfv
    #
    @25
    cvol
    cfv
    #
    @26
    cvol
    cfv
    #
    caddc
    co
    #
    @7
    @24
    @5
    @27
    cvol
    @24
    @27
    @5
    @24
    @13
    cB
    cxr
    wcel
    #
    @21
    @27
    @5
    wceq
    @0
    @1
    @13
    @21
    @14
    3ad2ant1
    @1
    @0
    @32
    @21
    cB
    rexr
    3ad2ant2
    @0
    @1
    @21
    simp3
    #
    cA
    cB
    snunioo2
    syl3anc
    eqcomd
    fveq2d
    @24
    @25
    cvol
    cdm
    #
    wcel
    #
    @26
    @34
    wcel
    #
    @25
    @26
    cin
    c0
    wceq
    #
    @29
    cr
    wcel
    #
    @30
    cr
    wcel
    #
    @28
    @31
    wceq
    @35
    @24
    cA
    cB
    ioombl
    a1i
    @1
    @0
    @36
    @21
    cB
    snmbl
    3ad2ant2
    @37
    @24
    @37
    cB
    @25
    wcel
    wn
    cA
    cB
    ubioo
    @25
    cB
    disjsn
    mpbir
    a1i
    @0
    @1
    @38
    @21
    cA
    cB
    ioovolcl
    3adant3
    @1
    @0
    @39
    @21
    @1
    @30
    cc0
    cr
    cB
    volsn
    #
    @1
    0red
    eqeltrd
    3ad2ant2
    @25
    @26
    volun
    syl32anc
    @24
    @31
    @7
    cc0
    caddc
    co
    @7
    @24
    @29
    @7
    @30
    cc0
    caddc
    @24
    @0
    @1
    @2
    @29
    @7
    wceq
    @0
    @1
    @21
    simp1
    #
    @0
    @1
    @21
    simp2
    #
    @24
    cA
    cB
    @41
    @42
    @33
    ltled
    cA
    cB
    volioo
    syl3anc
    @1
    @0
    @30
    cc0
    wceq
    @21
    @40
    3ad2ant2
    oveq12d
    @24
    @7
    @24
    cB
    cA
    @24
    cB
    @42
    recnd
    @0
    @1
    @17
    @21
    @18
    3ad2ant1
    subcld
    addid1d
    eqtrd
    3eqtrd
    syl3anc
    pm2.61dan
end
