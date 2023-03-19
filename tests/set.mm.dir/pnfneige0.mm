include "wcel.mm"
include "cpnf.mm"
include "wa.mm"
include "cv.mm"
include "cioc.mm"
include "co.mm"
include "cc0.mm"
include "cin.mm"
include "wss.mm"
include "cr.mm"
include "wrex.mm"
include "clt.mm"
include "wbr.mm"
include "cif.mm"
include "0red.mm"
include "wn.mm"
include "simpllr.mm"
include "ifclda.mm"
include "wceq.mm"
include "cxr.mm"
include "rexr.mm"
include "0xr.mm"
include "a1i.mm"
include "pnfxr.mm"
include "iocinif.mm"
include "syl3anc.mm"
include "ovif.mm"
include "syl6reqr.mm"
include "ad2antlr.mm"
include "cicc.mm"
include "iocssicc.mm"
include "sslin.mm"
include "mp1i.mm"
include "simpr.mm"
include "ssin.mm"
include "biimpri.mm"
include "simpld.mm"
include "ssinss1.mm"
include "3syl.mm"
include "sstrd.mm"
include "eqsstrd.mm"
include "oveq1.mm"
include "sseq1d.mm"
include "rspcev.mm"
include "syl2anc.mm"
include "cle.mm"
include "cordt.mm"
include "cfv.mm"
include "crest.mm"
include "ctop.mm"
include "cvv.mm"
include "ctopon.mm"
include "letopon.mm"
include "iccssxr.mm"
include "resttopon.mm"
include "mp2an.mm"
include "topontopi.mm"
include "ovex.mm"
include "cxrs.mm"
include "cress.mm"
include "ctopn.mm"
include "xrge0topn.mm"
include "eqtri.mm"
include "eleq2i.mm"
include "biimpi.mm"
include "elrestr.mm"
include "letop.mm"
include "restabs.mm"
include "mp3an.mm"
include "syl6eleq.mm"
include "wb.mm"
include "iocpnfordt.mm"
include "ssid.mm"
include "inss2.mm"
include "restopnb.mm"
include "syl23anc.mm"
include "mpbird.mm"
include "adantr.mm"
include "0ltpnf.mm"
include "ubioc1.mm"
include "elind.mm"
include "pnfnei.mm"
include "r19.29a.mm"

theorem pnfneige0
  let vx: setvar x
  let cA: class A
  let cJ: class J
  let vy: setvar y
  assume pnfneige0.j: |- J = ( TopOpen ` ( RR*s |`s ( 0 [,] +oo ) ) )

  disjoint A x
  disjoint x y
  disjoint A y
  disjoint J y
  assert |- ( ( A e. J /\ +oo e. A ) -> E. x e. RR ( x (,] +oo ) C_ A )

  proof
    cA
    cJ
    wcel
    #
    cpnf
    cA
    wcel
    #
    wa
    #
    vy
    cv
    #
    cpnf
    cioc
    co
    #
    cA
    cc0
    cpnf
    cioc
    co
    #
    cin
    #
    wss
    #
    vx
    cv
    #
    cpnf
    cioc
    co
    #
    cA
    wss
    #
    vx
    cr
    wrex
    #
    vy
    cr
    @2
    @3
    cr
    wcel
    #
    wa
    #
    @7
    wa
    #
    @3
    cc0
    clt
    wbr
    #
    cc0
    @3
    cif
    #
    cr
    wcel
    @16
    cpnf
    cioc
    co
    #
    cA
    wss
    #
    @11
    @14
    @15
    cc0
    @3
    cr
    @14
    @15
    wa
    0red
    @2
    @12
    @7
    @15
    wn
    simpllr
    ifclda
    @14
    @17
    @4
    @5
    cin
    #
    cA
    @12
    @17
    @19
    wceq
    @2
    @7
    @12
    @19
    @15
    @5
    @4
    cif
    #
    @17
    @12
    @3
    cxr
    wcel
    cc0
    cxr
    wcel
    #
    cpnf
    cxr
    wcel
    #
    @19
    @20
    wceq
    @3
    rexr
    @21
    @12
    0xr
    a1i
    @22
    @12
    pnfxr
    a1i
    @3
    cc0
    cpnf
    iocinif
    syl3anc
    @15
    cc0
    @3
    cpnf
    cioc
    ovif
    syl6reqr
    ad2antlr
    @14
    @19
    @4
    cc0
    cpnf
    cicc
    co
    #
    cin
    #
    cA
    @5
    @23
    wss
    #
    @19
    @24
    wss
    @14
    cc0
    cpnf
    iocssicc
    #
    @5
    @23
    @4
    sslin
    mp1i
    @14
    @7
    @4
    cA
    wss
    #
    @24
    cA
    wss
    @13
    @7
    simpr
    @7
    @27
    @4
    @5
    wss
    #
    @27
    @28
    wa
    @7
    @4
    cA
    @5
    ssin
    biimpri
    simpld
    @4
    @23
    cA
    ssinss1
    3syl
    sstrd
    eqsstrd
    @10
    @18
    vx
    @16
    cr
    @8
    @16
    wceq
    @9
    @17
    cA
    @8
    @16
    cpnf
    cioc
    oveq1
    sseq1d
    rspcev
    syl2anc
    @2
    @6
    cle
    cordt
    cfv
    #
    wcel
    #
    cpnf
    @6
    wcel
    @7
    vy
    cr
    wrex
    @0
    @30
    @1
    @0
    @30
    @6
    @29
    @5
    crest
    co
    #
    wcel
    #
    @0
    @6
    @29
    @23
    crest
    co
    #
    @5
    crest
    co
    #
    @31
    @0
    @33
    ctop
    wcel
    #
    @5
    cvv
    wcel
    #
    cA
    @33
    wcel
    #
    @6
    @34
    wcel
    @35
    @0
    @23
    @33
    @29
    cxr
    ctopon
    cfv
    wcel
    @23
    cxr
    wss
    @33
    @23
    ctopon
    cfv
    wcel
    letopon
    cc0
    cpnf
    iccssxr
    @23
    @29
    cxr
    resttopon
    mp2an
    topontopi
    a1i
    @36
    @0
    cc0
    cpnf
    cioc
    ovex
    a1i
    #
    @0
    @37
    cJ
    @33
    cA
    cJ
    cxrs
    @23
    cress
    co
    ctopn
    cfv
    @33
    pnfneige0.j
    xrge0topn
    eqtri
    eleq2i
    biimpi
    cA
    @5
    @33
    ctop
    cvv
    elrestr
    syl3anc
    @29
    ctop
    wcel
    #
    @25
    @23
    cvv
    wcel
    @34
    @31
    wceq
    letop
    @26
    cc0
    cpnf
    cicc
    ovex
    @5
    @23
    @29
    ctop
    cvv
    restabs
    mp3an
    syl6eleq
    @0
    @39
    @36
    @5
    @29
    wcel
    #
    @5
    @5
    wss
    #
    @6
    @5
    wss
    #
    @30
    @32
    wb
    @39
    @0
    letop
    a1i
    @38
    @40
    @0
    cc0
    iocpnfordt
    a1i
    @41
    @0
    @5
    ssid
    a1i
    @42
    @0
    cA
    @5
    inss2
    a1i
    @5
    @5
    @6
    @29
    cvv
    restopnb
    syl23anc
    mpbird
    adantr
    @2
    cA
    @5
    cpnf
    @0
    @1
    simpr
    cpnf
    @5
    wcel
    #
    @2
    @21
    @22
    cc0
    cpnf
    clt
    wbr
    @43
    0xr
    pnfxr
    0ltpnf
    cc0
    cpnf
    ubioc1
    mp3an
    a1i
    elind
    vy
    @6
    pnfnei
    syl2anc
    r19.29a
end
