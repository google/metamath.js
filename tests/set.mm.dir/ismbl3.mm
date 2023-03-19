include "cvol.mm"
include "cdm.mm"
include "wcel.mm"
include "cr.mm"
include "wss.mm"
include "cv.mm"
include "covol.mm"
include "cfv.mm"
include "cin.mm"
include "cdif.mm"
include "caddc.mm"
include "co.mm"
include "cle.mm"
include "wbr.mm"
include "wi.mm"
include "cpw.mm"
include "wral.mm"
include "wa.mm"
include "cxad.mm"
include "ismbl2.mm"
include "wceq.mm"
include "inss1.mm"
include "a1i.mm"
include "elpwi.mm"
include "adantr.mm"
include "simpr.mm"
include "ovolsscl.mm"
include "syl3anc.mm"
include "difssd.mm"
include "rexaddd.mm"
include "adantlr.mm"
include "id.mm"
include "imp.mm"
include "adantll.mm"
include "eqbrtrd.mm"
include "wn.mm"
include "cpnf.mm"
include "cxr.mm"
include "syl5ss.mm"
include "ovolcl.mm"
include "syl.mm"
include "ssdifssd.mm"
include "xaddcld.mm"
include "pnfge.mm"
include "cc0.mm"
include "cicc.mm"
include "ovolf.mm"
include "ffvelrni.mm"
include "xrge0nre.mm"
include "syl2anc.mm"
include "eqcomd.mm"
include "breqtrd.mm"
include "pm2.61dan.mm"
include "ex.mm"
include "w3a.mm"
include "3adant2.mm"
include "simp2.mm"
include "3exp.mm"
include "impbid.mm"
include "ralbiia.mm"
include "anbi2i.mm"
include "bitri.mm"

theorem ismbl3
  let vx: setvar x
  let cA: class A
  let vk: setvar k

  disjoint A x
  disjoint k x
  assert |- ( A e. dom vol <-> ( A C_ RR /\ A. x e. ~P RR ( ( vol* ` ( x i^i A ) ) +e ( vol* ` ( x \ A ) ) ) <_ ( vol* ` x ) ) )

  proof
    cA
    cvol
    cdm
    wcel
    cA
    cr
    wss
    #
    vx
    cv
    #
    covol
    cfv
    #
    cr
    wcel
    #
    @1
    cA
    cin
    #
    covol
    cfv
    #
    @1
    cA
    cdif
    #
    covol
    cfv
    #
    caddc
    co
    #
    @2
    cle
    wbr
    #
    wi
    #
    vx
    cr
    cpw
    #
    wral
    #
    wa
    @0
    @5
    @7
    cxad
    co
    #
    @2
    cle
    wbr
    #
    vx
    @11
    wral
    #
    wa
    vx
    cA
    ismbl2
    @12
    @15
    @0
    @10
    @14
    vx
    @11
    @1
    @11
    wcel
    #
    @10
    @14
    @16
    @10
    @14
    @16
    @10
    wa
    #
    @3
    @14
    @17
    @3
    wa
    @13
    @8
    @2
    cle
    @16
    @3
    @13
    @8
    wceq
    @10
    @16
    @3
    wa
    #
    @5
    @7
    @18
    @4
    @1
    wss
    #
    @1
    cr
    wss
    #
    @3
    @5
    cr
    wcel
    @19
    @18
    @1
    cA
    inss1
    #
    a1i
    @16
    @20
    @3
    @1
    cr
    elpwi
    #
    adantr
    #
    @16
    @3
    simpr
    #
    @4
    @1
    ovolsscl
    syl3anc
    @18
    @6
    @1
    wss
    @20
    @3
    @7
    cr
    wcel
    @18
    @1
    cA
    difssd
    @23
    @24
    @6
    @1
    ovolsscl
    syl3anc
    rexaddd
    #
    adantlr
    @10
    @3
    @9
    @16
    @10
    @3
    @9
    @10
    id
    imp
    adantll
    eqbrtrd
    @16
    @3
    wn
    #
    @14
    @10
    @16
    @26
    wa
    #
    @13
    cpnf
    @2
    cle
    @16
    @13
    cpnf
    cle
    wbr
    #
    @26
    @16
    @13
    cxr
    wcel
    @28
    @16
    @5
    @7
    @16
    @4
    cr
    wss
    @5
    cxr
    wcel
    @16
    @4
    @1
    cr
    @21
    @22
    syl5ss
    @4
    ovolcl
    syl
    @16
    @6
    cr
    wss
    @7
    cxr
    wcel
    @16
    @1
    cr
    cA
    @22
    ssdifssd
    @6
    ovolcl
    syl
    xaddcld
    @13
    pnfge
    syl
    adantr
    @27
    @2
    cpnf
    @27
    @2
    cc0
    cpnf
    cicc
    co
    #
    wcel
    #
    @26
    @2
    cpnf
    wceq
    @16
    @30
    @26
    @11
    @29
    @1
    covol
    ovolf
    ffvelrni
    adantr
    @16
    @26
    simpr
    @2
    xrge0nre
    syl2anc
    eqcomd
    breqtrd
    adantlr
    pm2.61dan
    ex
    @16
    @14
    @3
    @9
    @16
    @14
    @3
    w3a
    @8
    @13
    @2
    cle
    @16
    @3
    @8
    @13
    wceq
    @14
    @18
    @13
    @8
    @25
    eqcomd
    3adant2
    @16
    @14
    @3
    simp2
    eqbrtrd
    3exp
    impbid
    ralbiia
    anbi2i
    bitri
end
