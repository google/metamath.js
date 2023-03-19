include "ct1.mm"
include "wcel.mm"
include "wss.mm"
include "wa.mm"
include "ccl.mm"
include "cfv.mm"
include "clp.mm"
include "cv.mm"
include "csn.mm"
include "cdif.mm"
include "ctop.mm"
include "t1top.mm"
include "clsss3.mm"
include "ssdifssd.mm"
include "syldan.mm"
include "sylan.mm"
include "sseld.mm"
include "wi.mm"
include "ccld.mm"
include "ssdifss.mm"
include "clscld.mm"
include "syl2an.mm"
include "adantr.mm"
include "cun.mm"
include "t1sncld.mm"
include "adantlr.mm"
include "uncld.mm"
include "syl2anc.mm"
include "sscls.mm"
include "ssundif.mm"
include "sylibr.mm"
include "clsss2.mm"
include "sylib.mm"
include "ex.mm"
include "com23.mm"
include "mpdd.mm"
include "ssdifd.mm"
include "clsss.mm"
include "syl3anc.mm"
include "impbid.mm"
include "wb.mm"
include "islp.mm"
include "3bitr4d.mm"
include "eqrdv.mm"

theorem lpcls
  let cS: class S
  let cJ: class J
  let cX: class X
  let vx: setvar x
  assume lpcls.1: |- X = U. J


  assert |- ( ( J e. Fre /\ S C_ X ) -> ( ( limPt ` J ) ` ( ( cls ` J ) ` S ) ) = ( ( limPt ` J ) ` S ) )

  proof
    cJ
    ct1
    wcel
    #
    cS
    cX
    wss
    #
    wa
    #
    vx
    cS
    cJ
    ccl
    cfv
    #
    cfv
    #
    cJ
    clp
    cfv
    #
    cfv
    #
    cS
    @5
    cfv
    #
    @2
    vx
    cv
    #
    @4
    @8
    csn
    #
    cdif
    #
    @3
    cfv
    #
    wcel
    #
    @8
    cS
    @9
    cdif
    #
    @3
    cfv
    #
    wcel
    #
    @8
    @6
    wcel
    #
    @8
    @7
    wcel
    #
    @2
    @12
    @15
    @2
    @12
    @8
    cX
    wcel
    #
    @15
    @2
    @11
    cX
    @8
    @0
    cJ
    ctop
    wcel
    #
    @1
    @11
    cX
    wss
    #
    cJ
    t1top
    #
    @19
    @1
    @10
    cX
    wss
    #
    @20
    @19
    @1
    wa
    @4
    cX
    @9
    cS
    cJ
    cX
    lpcls.1
    clsss3
    #
    ssdifssd
    @10
    cJ
    cX
    lpcls.1
    clsss3
    syldan
    sylan
    sseld
    @2
    @18
    @12
    @15
    @2
    @18
    @12
    @15
    wi
    @2
    @18
    wa
    #
    @11
    @14
    @8
    @24
    @14
    cJ
    ccld
    cfv
    #
    wcel
    #
    @10
    @14
    wss
    #
    @11
    @14
    wss
    @2
    @26
    @18
    @0
    @19
    @13
    cX
    wss
    #
    @26
    @1
    @21
    cS
    cX
    @9
    ssdifss
    #
    @13
    cJ
    cX
    lpcls.1
    clscld
    syl2an
    adantr
    #
    @24
    @4
    @9
    @14
    cun
    #
    wss
    #
    @27
    @24
    @31
    @25
    wcel
    #
    cS
    @31
    wss
    #
    @32
    @24
    @9
    @25
    wcel
    #
    @26
    @33
    @0
    @18
    @35
    @1
    @8
    cJ
    cX
    lpcls.1
    t1sncld
    adantlr
    @30
    @9
    @14
    cJ
    uncld
    syl2anc
    @2
    @34
    @18
    @2
    @13
    @14
    wss
    #
    @34
    @0
    @19
    @28
    @36
    @1
    @21
    @29
    @13
    cJ
    cX
    lpcls.1
    sscls
    syl2an
    cS
    @9
    @14
    ssundif
    sylibr
    adantr
    @31
    cS
    cJ
    cX
    lpcls.1
    clsss2
    syl2anc
    @4
    @9
    @14
    ssundif
    sylib
    @14
    @10
    cJ
    cX
    lpcls.1
    clsss2
    syl2anc
    sseld
    ex
    com23
    mpdd
    @2
    @14
    @11
    @8
    @2
    @19
    @22
    @13
    @10
    wss
    @14
    @11
    wss
    @0
    @19
    @1
    @21
    adantr
    @2
    @4
    cX
    @9
    @0
    @19
    @1
    @4
    cX
    wss
    #
    @21
    @23
    sylan
    ssdifssd
    @2
    cS
    @4
    @9
    @0
    @19
    @1
    cS
    @4
    wss
    @21
    cS
    cJ
    cX
    lpcls.1
    sscls
    sylan
    ssdifd
    @10
    @13
    cJ
    cX
    lpcls.1
    clsss
    syl3anc
    sseld
    impbid
    @0
    @19
    @1
    @16
    @12
    wb
    #
    @21
    @19
    @1
    @37
    @38
    @23
    @8
    @4
    cJ
    cX
    lpcls.1
    islp
    syldan
    sylan
    @0
    @19
    @1
    @17
    @15
    wb
    @21
    @8
    cS
    cJ
    cX
    lpcls.1
    islp
    sylan
    3bitr4d
    eqrdv
end
