include "cr.mm"
include "wss.mm"
include "cv.mm"
include "cle.mm"
include "wbr.mm"
include "wral.mm"
include "w3a.mm"
include "wa.mm"
include "wrex.mm"
include "wi.mm"
include "cin.mm"
include "c0.mm"
include "wceq.mm"
include "clt.mm"
include "simpr1.mm"
include "simpr2.mm"
include "wcel.mm"
include "wne.mm"
include "wn.mm"
include "simp1.mm"
include "simpl.mm"
include "disjel.mm"
include "syl2an.mm"
include "weq.mm"
include "eleq1.mm"
include "biimpcd.mm"
include "necon3bd.mm"
include "ad2antll.mm"
include "mpd.mm"
include "simp2.mm"
include "ssel2.mm"
include "simp3.mm"
include "simpr.mm"
include "ltlend.mm"
include "biimprd.mm"
include "mpan2d.mm"
include "ralimdvva.mm"
include "3exp.mm"
include "3imp2.mm"
include "dedekind.mm"
include "syl3anc.mm"
include "ex.mm"
include "wex.mm"
include "n0.mm"
include "inss1.mm"
include "sseli.mm"
include "nfv.mm"
include "nfra1.mm"
include "nf3an.mm"
include "nfan.mm"
include "nfra2.mm"
include "rsp.mm"
include "inss2.mm"
include "breq2.mm"
include "rspccv.mm"
include "syl5.mm"
include "syl6.mm"
include "com23.mm"
include "imp32.mm"
include "3ad2antl3.mm"
include "adantr.mm"
include "breq1.mm"
include "ralbidv.mm"
include "rspccva.mm"
include "r19.21bi.mm"
include "jca.mm"
include "ralrimi.mm"
include "expr.mm"
include "anbi12d.mm"
include "2ralbidv.mm"
include "rspcev.mm"
include "syl2anc.mm"
include "expcom.mm"
include "exlimiv.mm"
include "sylbi.mm"
include "pm2.61ine.mm"

theorem dedekindle
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let vw: setvar w

  disjoint A x
  disjoint A y
  disjoint A z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint B x
  disjoint B y
  disjoint B z
  disjoint A w
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint B w
  assert |- ( ( A C_ RR /\ B C_ RR /\ A. x e. A A. y e. B x <_ y ) -> E. z e. RR A. x e. A A. y e. B ( x <_ z /\ z <_ y ) )

  proof
    cA
    cr
    wss
    #
    cB
    cr
    wss
    #
    vx
    cv
    #
    vy
    cv
    #
    cle
    wbr
    #
    vy
    cB
    wral
    #
    vx
    cA
    wral
    #
    w3a
    #
    @2
    vz
    cv
    #
    cle
    wbr
    #
    @8
    @3
    cle
    wbr
    #
    wa
    #
    vy
    cB
    wral
    vx
    cA
    wral
    #
    vz
    cr
    wrex
    #
    wi
    #
    cA
    cB
    cin
    #
    c0
    @15
    c0
    wceq
    #
    @7
    @13
    @16
    @7
    wa
    @0
    @1
    @2
    @3
    clt
    wbr
    #
    vy
    cB
    wral
    vx
    cA
    wral
    #
    @13
    @16
    @0
    @1
    @6
    simpr1
    @16
    @0
    @1
    @6
    simpr2
    @16
    @0
    @1
    @6
    @18
    @16
    @0
    @1
    @6
    @18
    wi
    @16
    @0
    @1
    w3a
    #
    @4
    @17
    vx
    vy
    cA
    cB
    @19
    @2
    cA
    wcel
    #
    @3
    cB
    wcel
    #
    wa
    #
    wa
    #
    @4
    @3
    @2
    wne
    #
    @17
    @23
    @2
    cB
    wcel
    #
    wn
    #
    @24
    @19
    @16
    @20
    @26
    @22
    @16
    @0
    @1
    simp1
    @20
    @21
    simpl
    #
    cA
    cB
    @2
    disjel
    syl2an
    @21
    @26
    @24
    wi
    @19
    @20
    @21
    @25
    @3
    @2
    vy
    vx
    weq
    @21
    @25
    @3
    @2
    cB
    eleq1
    biimpcd
    necon3bd
    ad2antll
    mpd
    @23
    @17
    @4
    @24
    wa
    @23
    @2
    @3
    @19
    @0
    @20
    @2
    cr
    wcel
    @22
    @16
    @0
    @1
    simp2
    @27
    cA
    cr
    @2
    ssel2
    syl2an
    @19
    @1
    @21
    @3
    cr
    wcel
    @22
    @16
    @0
    @1
    simp3
    @20
    @21
    simpr
    cB
    cr
    @3
    ssel2
    syl2an
    ltlend
    biimprd
    mpan2d
    ralimdvva
    3exp
    3imp2
    vx
    vy
    vz
    cA
    cB
    dedekind
    syl3anc
    ex
    @15
    c0
    wne
    vw
    cv
    #
    @15
    wcel
    #
    vw
    wex
    @14
    vw
    @15
    n0
    @29
    @14
    vw
    @7
    @29
    @13
    @7
    @29
    wa
    #
    @28
    cr
    wcel
    #
    @2
    @28
    cle
    wbr
    #
    @28
    @3
    cle
    wbr
    #
    wa
    #
    vy
    cB
    wral
    #
    vx
    cA
    wral
    #
    @13
    @7
    @0
    @28
    cA
    wcel
    #
    @31
    @29
    @0
    @1
    @6
    simp1
    @15
    cA
    @28
    cA
    cB
    inss1
    sseli
    #
    cA
    cr
    @28
    ssel2
    syl2an
    @30
    @35
    vx
    cA
    @7
    @29
    vx
    @0
    @1
    @6
    vx
    @0
    vx
    nfv
    @1
    vx
    nfv
    @5
    vx
    cA
    nfra1
    nf3an
    @29
    vx
    nfv
    nfan
    @7
    @29
    @20
    @35
    @7
    @29
    @20
    wa
    #
    wa
    #
    @34
    vy
    cB
    @7
    @39
    vy
    @0
    @1
    @6
    vy
    @0
    vy
    nfv
    @1
    vy
    nfv
    @4
    vx
    vy
    cA
    cB
    nfra2
    nf3an
    @39
    vy
    nfv
    nfan
    @40
    @21
    @34
    @40
    @21
    wa
    @32
    @33
    @40
    @32
    @21
    @6
    @0
    @39
    @32
    @1
    @6
    @29
    @20
    @32
    @6
    @20
    @29
    @32
    @6
    @20
    @5
    @29
    @32
    wi
    @5
    vx
    cA
    rsp
    @29
    @28
    cB
    wcel
    @5
    @32
    @15
    cB
    @28
    cA
    cB
    inss2
    sseli
    @4
    @32
    vy
    @28
    cB
    @3
    @28
    @2
    cle
    breq2
    rspccv
    syl5
    syl6
    com23
    imp32
    3ad2antl3
    adantr
    @40
    @33
    vy
    cB
    @7
    @6
    @37
    @33
    vy
    cB
    wral
    #
    @39
    @0
    @1
    @6
    simp3
    @29
    @37
    @20
    @38
    adantr
    @5
    @41
    vx
    @28
    cA
    vx
    vw
    weq
    @4
    @33
    vy
    cB
    @2
    @28
    @3
    cle
    breq1
    ralbidv
    rspccva
    syl2an
    r19.21bi
    jca
    ex
    ralrimi
    expr
    ralrimi
    @12
    @36
    vz
    @28
    cr
    vz
    vw
    weq
    #
    @11
    @34
    vx
    vy
    cA
    cB
    @42
    @9
    @32
    @10
    @33
    @8
    @28
    @2
    cle
    breq2
    @8
    @28
    @3
    cle
    breq1
    anbi12d
    2ralbidv
    rspcev
    syl2anc
    expcom
    exlimiv
    sylbi
    pm2.61ine
end
