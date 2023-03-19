include "cxr.mm"
include "wss.mm"
include "cpnf.mm"
include "csn.mm"
include "cun.mm"
include "clt.mm"
include "cinf.mm"
include "id.mm"
include "wcel.mm"
include "pnfxr.mm"
include "snssi.mm"
include "ax-mp.mm"
include "a1i.mm"
include "unssd.mm"
include "infxrcld.mm"
include "infxrcl.mm"
include "cle.mm"
include "wbr.mm"
include "ssun1.mm"
include "infxrss.mm"
include "syl2anc.mm"
include "c0.mm"
include "wceq.mm"
include "infeq1.mm"
include "xrinf0.mm"
include "eqeltri.mm"
include "eqeltrd.mm"
include "wor.mm"
include "xrltso.mm"
include "infsn.mm"
include "mp2an.mm"
include "eqcomi.mm"
include "syl6eq.mm"
include "uneq1.mm"
include "0un.mm"
include "eqtrd.mm"
include "infeq1d.mm"
include "3eqtr4d.mm"
include "xreqled.mm"
include "adantl.mm"
include "wn.mm"
include "wne.mm"
include "neqne.mm"
include "wa.mm"
include "nfv.mm"
include "simpl.mm"
include "syl.mm"
include "cv.mm"
include "wrex.mm"
include "simpr.mm"
include "ssel2.mm"
include "xrleid.mm"
include "breq1.mm"
include "rspcev.mm"
include "ad4ant14.mm"
include "simpll.mm"
include "elunnel1.mm"
include "elsni.mm"
include "adantll.mm"
include "wral.mm"
include "simplr.mm"
include "pnfge.mm"
include "adantlr.mm"
include "breqtrrd.mm"
include "ralrimiva.mm"
include "r19.2z.mm"
include "pm2.61dan.mm"
include "infleinf2.mm"
include "sylan2.mm"
include "xrletrid.mm"

theorem infxrpnf
  let cA: class A
  let vx: setvar x
  let vy: setvar y


  assert |- ( A C_ RR* -> inf ( ( A u. { +oo } ) , RR* , < ) = inf ( A , RR* , < ) )

  proof
    cA
    cxr
    wss
    #
    cA
    cpnf
    csn
    #
    cun
    #
    cxr
    clt
    cinf
    #
    cA
    cxr
    clt
    cinf
    #
    @0
    @2
    @0
    cA
    @1
    cxr
    @0
    id
    @1
    cxr
    wss
    #
    @0
    cpnf
    cxr
    wcel
    #
    @5
    pnfxr
    cpnf
    cxr
    snssi
    ax-mp
    a1i
    unssd
    #
    infxrcld
    cA
    infxrcl
    @0
    cA
    @2
    wss
    #
    @2
    cxr
    wss
    #
    @3
    @4
    cle
    wbr
    @8
    @0
    cA
    @1
    ssun1
    a1i
    @7
    cA
    @2
    infxrss
    syl2anc
    @0
    cA
    c0
    wceq
    #
    @4
    @3
    cle
    wbr
    #
    @10
    @11
    @0
    @10
    @4
    @3
    @10
    @4
    c0
    cxr
    clt
    cinf
    #
    cxr
    cxr
    cA
    c0
    clt
    infeq1
    #
    @12
    cxr
    wcel
    @10
    @12
    cpnf
    cxr
    xrinf0
    pnfxr
    eqeltri
    a1i
    eqeltrd
    @10
    cpnf
    @1
    cxr
    clt
    cinf
    #
    @4
    @3
    cpnf
    @14
    wceq
    @10
    @14
    cpnf
    cxr
    clt
    wor
    @6
    @14
    cpnf
    wceq
    xrltso
    pnfxr
    cxr
    cpnf
    clt
    infsn
    mp2an
    eqcomi
    a1i
    @10
    @4
    @12
    cpnf
    @13
    xrinf0
    syl6eq
    @10
    cxr
    @2
    @1
    clt
    @10
    @2
    c0
    @1
    cun
    #
    @1
    cA
    c0
    @1
    uneq1
    @15
    @1
    wceq
    @10
    @1
    0un
    a1i
    eqtrd
    infeq1d
    3eqtr4d
    xreqled
    adantl
    @10
    wn
    @0
    cA
    c0
    wne
    #
    @11
    cA
    c0
    neqne
    @0
    @16
    wa
    #
    vx
    vy
    cA
    @2
    @17
    vx
    nfv
    @17
    vy
    nfv
    @0
    @16
    simpl
    #
    @17
    @0
    @9
    @18
    @7
    syl
    @17
    vx
    cv
    #
    @2
    wcel
    #
    wa
    #
    @19
    cA
    wcel
    #
    vy
    cv
    #
    @19
    cle
    wbr
    #
    vy
    cA
    wrex
    #
    @0
    @22
    @25
    @16
    @20
    @0
    @22
    wa
    #
    @22
    @19
    @19
    cle
    wbr
    #
    @25
    @0
    @22
    simpr
    @26
    @19
    cxr
    wcel
    @27
    cA
    cxr
    @19
    ssel2
    @19
    xrleid
    syl
    @24
    @27
    vy
    @19
    cA
    @23
    @19
    @19
    cle
    breq1
    rspcev
    syl2anc
    ad4ant14
    @21
    @22
    wn
    #
    wa
    @17
    @19
    cpnf
    wceq
    #
    @25
    @17
    @20
    @28
    simpll
    @20
    @28
    @29
    @17
    @20
    @28
    wa
    @19
    @1
    wcel
    @29
    @19
    cA
    @1
    elunnel1
    @19
    cpnf
    elsni
    syl
    adantll
    @17
    @29
    wa
    @16
    @24
    vy
    cA
    wral
    #
    @25
    @0
    @16
    @29
    simplr
    @0
    @29
    @30
    @16
    @0
    @29
    wa
    #
    @24
    vy
    cA
    @31
    @23
    cA
    wcel
    #
    wa
    @23
    cpnf
    @19
    cle
    @0
    @32
    @23
    cpnf
    cle
    wbr
    #
    @29
    @0
    @32
    wa
    @23
    cxr
    wcel
    @33
    cA
    cxr
    @23
    ssel2
    @23
    pnfge
    syl
    adantlr
    @0
    @29
    @32
    simplr
    breqtrrd
    ralrimiva
    adantlr
    @24
    vy
    cA
    r19.2z
    syl2anc
    syl2anc
    pm2.61dan
    infleinf2
    sylan2
    pm2.61dan
    xrletrid
end
