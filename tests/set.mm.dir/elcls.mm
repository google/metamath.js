include "ctop.mm"
include "wcel.mm"
include "wss.mm"
include "w3a.mm"
include "ccl.mm"
include "cfv.mm"
include "cv.mm"
include "cin.mm"
include "c0.mm"
include "wne.mm"
include "wi.mm"
include "wral.mm"
include "wn.mm"
include "wa.mm"
include "wrex.mm"
include "cdif.mm"
include "cmclsopn.mm"
include "3adant3.mm"
include "adantr.mm"
include "eldif.mm"
include "biimpri.mm"
include "3ad2antl3.mm"
include "wceq.mm"
include "simpr.mm"
include "sscls.mm"
include "ssind.mm"
include "dfin4.mm"
include "syl6sseq.mm"
include "wb.mm"
include "reldisj.mm"
include "adantl.mm"
include "mpbird.mm"
include "nne.mm"
include "incom.mm"
include "eqeq1i.mm"
include "bitri.mm"
include "sylibr.mm"
include "eleq2.mm"
include "ineq1.mm"
include "neeq1d.mm"
include "notbid.mm"
include "anbi12d.mm"
include "rspcev.mm"
include "syl12anc.mm"
include "df-ne.mm"
include "con2bii.mm"
include "ccld.mm"
include "opncld.mm"
include "adantlr.mm"
include "biimpa.mm"
include "adantll.mm"
include "clsss2.mm"
include "syl2anc.mm"
include "sseld.mm"
include "eldifn.mm"
include "syl6.mm"
include "con2d.mm"
include "sylan2br.mm"
include "exp31.mm"
include "com34.mm"
include "imp4a.mm"
include "rexlimdv.mm"
include "imp.mm"
include "3adantl3.mm"
include "impbida.mm"
include "rexanali.mm"
include "syl6bb.mm"
include "con4bid.mm"

theorem elcls
  let vx: setvar x
  let cP: class P
  let cS: class S
  let cJ: class J
  let cX: class X
  let vy: setvar y
  let vz: setvar z
  let cU: class U
  let cT: class T
  let cA: class A
  assume clscld.1: |- X = U. J

  disjoint J x
  disjoint P x
  disjoint S x
  disjoint X x
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint J y
  disjoint J z
  disjoint S y
  disjoint S z
  disjoint U x
  disjoint X y
  disjoint X z
  disjoint T x
  disjoint A x
  assert |- ( ( J e. Top /\ S C_ X /\ P e. X ) -> ( P e. ( ( cls ` J ) ` S ) <-> A. x e. J ( P e. x -> ( x i^i S ) =/= (/) ) ) )

  proof
    cJ
    ctop
    wcel
    #
    cS
    cX
    wss
    #
    cP
    cX
    wcel
    #
    w3a
    #
    cP
    cS
    cJ
    ccl
    cfv
    cfv
    #
    wcel
    #
    cP
    vx
    cv
    #
    wcel
    #
    @6
    cS
    cin
    #
    c0
    wne
    #
    wi
    vx
    cJ
    wral
    #
    @3
    @5
    wn
    #
    @7
    @9
    wn
    #
    wa
    #
    vx
    cJ
    wrex
    #
    @10
    wn
    @3
    @11
    @14
    @3
    @11
    wa
    cX
    @4
    cdif
    #
    cJ
    wcel
    #
    cP
    @15
    wcel
    #
    @15
    cS
    cin
    #
    c0
    wne
    #
    wn
    #
    @14
    @3
    @16
    @11
    @0
    @1
    @16
    @2
    cS
    cJ
    cX
    clscld.1
    cmclsopn
    3adant3
    adantr
    @2
    @0
    @11
    @17
    @1
    @17
    @2
    @11
    wa
    cP
    cX
    @4
    eldif
    biimpri
    3ad2antl3
    @3
    @20
    @11
    @0
    @1
    @20
    @2
    @0
    @1
    wa
    #
    cS
    @15
    cin
    #
    c0
    wceq
    #
    @20
    @21
    @23
    cS
    cX
    @15
    cdif
    #
    wss
    #
    @21
    cS
    cX
    @4
    cin
    @24
    @21
    cS
    cX
    @4
    @0
    @1
    simpr
    cS
    cJ
    cX
    clscld.1
    sscls
    ssind
    cX
    @4
    dfin4
    syl6sseq
    @1
    @23
    @25
    wb
    @0
    cS
    @15
    cX
    reldisj
    adantl
    mpbird
    @20
    @18
    c0
    wceq
    @23
    @18
    c0
    nne
    @18
    @22
    c0
    @15
    cS
    incom
    eqeq1i
    bitri
    sylibr
    3adant3
    adantr
    @13
    @17
    @20
    wa
    vx
    @15
    cJ
    @6
    @15
    wceq
    #
    @7
    @17
    @12
    @20
    @6
    @15
    cP
    eleq2
    @26
    @9
    @19
    @26
    @8
    @18
    c0
    @6
    @15
    cS
    ineq1
    neeq1d
    notbid
    anbi12d
    rspcev
    syl12anc
    @0
    @1
    @14
    @11
    @2
    @21
    @14
    @11
    @21
    @13
    @11
    vx
    cJ
    @21
    @6
    cJ
    wcel
    #
    @7
    @12
    @11
    @21
    @27
    @12
    @7
    @11
    @21
    @27
    @12
    @7
    @11
    wi
    #
    @12
    @21
    @27
    wa
    #
    cS
    @6
    cin
    #
    c0
    wceq
    #
    @28
    @31
    @8
    c0
    wceq
    #
    @12
    @30
    @8
    c0
    cS
    @6
    incom
    eqeq1i
    @9
    @32
    @8
    c0
    df-ne
    con2bii
    bitri
    @29
    @31
    wa
    #
    @5
    @7
    @33
    @5
    cP
    cX
    @6
    cdif
    #
    wcel
    @7
    wn
    @33
    @4
    @34
    cP
    @33
    @34
    cJ
    ccld
    cfv
    wcel
    #
    cS
    @34
    wss
    #
    @4
    @34
    wss
    @29
    @35
    @31
    @0
    @27
    @35
    @1
    @6
    cJ
    cX
    clscld.1
    opncld
    adantlr
    adantr
    @21
    @31
    @36
    @27
    @1
    @31
    @36
    @0
    @1
    @31
    @36
    cS
    @6
    cX
    reldisj
    biimpa
    adantll
    adantlr
    @34
    cS
    cJ
    cX
    clscld.1
    clsss2
    syl2anc
    sseld
    cP
    cX
    @6
    eldifn
    syl6
    con2d
    sylan2br
    exp31
    com34
    imp4a
    rexlimdv
    imp
    3adantl3
    impbida
    @7
    @9
    vx
    cJ
    rexanali
    syl6bb
    con4bid
end
