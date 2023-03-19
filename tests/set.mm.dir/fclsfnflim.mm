include "cfil.mm"
include "cfv.mm"
include "wcel.mm"
include "cfcls.mm"
include "co.mm"
include "cv.mm"
include "wss.mm"
include "cflim.mm"
include "wa.mm"
include "wrex.mm"
include "csn.mm"
include "cnei.mm"
include "cun.mm"
include "cfi.mm"
include "cfg.mm"
include "cfbas.mm"
include "cpw.mm"
include "c0.mm"
include "wne.mm"
include "wn.mm"
include "filsspw.mm"
include "adantr.mm"
include "cuni.mm"
include "ctop.mm"
include "fclstop.mm"
include "adantl.mm"
include "eqid.mm"
include "neisspw.mm"
include "syl.mm"
include "filunibas.mm"
include "wceq.mm"
include "fclsfil.mm"
include "sylan9req.mm"
include "pweqd.mm"
include "sseqtr4d.mm"
include "unssd.mm"
include "ssun1.mm"
include "filn0.mm"
include "ssn0.mm"
include "sylancr.mm"
include "cin.mm"
include "wral.mm"
include "w3a.mm"
include "incom.mm"
include "fclsneii.mm"
include "syl5eqner.mm"
include "3com23.mm"
include "3expb.mm"
include "adantll.mm"
include "ralrimivva.mm"
include "wb.mm"
include "filfbas.mm"
include "ctopon.mm"
include "istopon.mm"
include "sylanbrc.mm"
include "fclselbas.mm"
include "eleqtrrd.mm"
include "snssd.mm"
include "snnzg.mm"
include "neifil.mm"
include "syl3anc.mm"
include "fbunfip.mm"
include "syl2anc.mm"
include "mpbird.mm"
include "filtop.mm"
include "fsubbas.mm"
include "mpbir3and.mm"
include "fgcl.mm"
include "cvv.mm"
include "fvex.mm"
include "unexg.mm"
include "mpan2.mm"
include "ssfii.mm"
include "unssad.mm"
include "ssfg.mm"
include "sstrd.mm"
include "unssbd.mm"
include "elflim.mm"
include "mpbir2and.mm"
include "sseq2.mm"
include "oveq2.mm"
include "eleq2d.mm"
include "anbi12d.mm"
include "rspcev.mm"
include "syl12anc.mm"
include "ex.mm"
include "simprl.mm"
include "simprrr.mm"
include "flimtopon.mm"
include "simpl.mm"
include "simprrl.mm"
include "fclsss2.mm"
include "flimfcls.mm"
include "sseldi.mm"
include "sseldd.mm"
include "rexlimdvaa.mm"
include "impbid.mm"

theorem fclsfnflim
  let cA: class A
  let vg: setvar g
  let cF: class F
  let cJ: class J
  let cX: class X
  let vo: setvar o
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z

  disjoint A g
  disjoint F g
  disjoint J g
  disjoint X g
  disjoint g o
  disjoint g x
  disjoint g y
  disjoint g z
  disjoint o x
  disjoint o y
  disjoint o z
  disjoint A o
  disjoint x y
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint F o
  disjoint F x
  disjoint F y
  disjoint F z
  disjoint J o
  disjoint J x
  disjoint J y
  disjoint J z
  disjoint X o
  disjoint X x
  disjoint X y
  disjoint X z
  assert |- ( F e. ( Fil ` X ) -> ( A e. ( J fClus F ) <-> E. g e. ( Fil ` X ) ( F C_ g /\ A e. ( J fLim g ) ) ) )

  proof
    cF
    cX
    cfil
    cfv
    #
    wcel
    #
    cA
    cJ
    cF
    cfcls
    co
    #
    wcel
    #
    cF
    vg
    cv
    #
    wss
    #
    cA
    cJ
    @4
    cflim
    co
    #
    wcel
    #
    wa
    #
    vg
    @0
    wrex
    #
    @1
    @3
    @9
    @1
    @3
    wa
    #
    cX
    cF
    cA
    csn
    #
    cJ
    cnei
    cfv
    #
    cfv
    #
    cun
    #
    cfi
    cfv
    #
    cfg
    co
    #
    @0
    wcel
    #
    cF
    @16
    wss
    #
    cA
    cJ
    @16
    cflim
    co
    #
    wcel
    #
    @9
    @10
    @15
    cX
    cfbas
    cfv
    #
    wcel
    #
    @17
    @10
    @22
    @14
    cX
    cpw
    #
    wss
    #
    @14
    c0
    wne
    #
    c0
    @15
    wcel
    wn
    #
    @10
    cF
    @13
    @23
    @1
    cF
    @23
    wss
    @3
    cF
    cX
    filsspw
    adantr
    @10
    @13
    cJ
    cuni
    #
    cpw
    #
    @23
    @10
    cJ
    ctop
    wcel
    #
    @13
    @28
    wss
    @3
    @29
    @1
    cA
    cF
    cJ
    fclstop
    adantl
    #
    @11
    cJ
    @27
    @27
    eqid
    #
    neisspw
    syl
    @10
    cX
    @27
    @1
    @3
    cX
    cF
    cuni
    #
    @27
    cF
    cX
    filunibas
    @3
    cF
    @27
    cfil
    cfv
    wcel
    @32
    @27
    wceq
    cA
    cF
    cJ
    @27
    @31
    fclsfil
    cF
    @27
    filunibas
    syl
    sylan9req
    #
    pweqd
    sseqtr4d
    unssd
    @1
    @25
    @3
    @1
    cF
    @14
    wss
    cF
    c0
    wne
    @25
    cF
    @13
    ssun1
    cF
    cX
    filn0
    cF
    @14
    ssn0
    sylancr
    adantr
    @10
    @26
    vx
    cv
    #
    vy
    cv
    #
    cin
    #
    c0
    wne
    #
    vy
    @13
    wral
    vx
    cF
    wral
    #
    @10
    @37
    vx
    vy
    cF
    @13
    @3
    @34
    cF
    wcel
    #
    @35
    @13
    wcel
    #
    wa
    @37
    @1
    @3
    @39
    @40
    @37
    @3
    @40
    @39
    @37
    @3
    @40
    @39
    w3a
    @36
    @35
    @34
    cin
    c0
    @35
    @34
    incom
    cA
    @34
    cF
    cJ
    @35
    fclsneii
    syl5eqner
    3com23
    3expb
    adantll
    ralrimivva
    @10
    cF
    @21
    wcel
    #
    @13
    @21
    wcel
    #
    @26
    @38
    wb
    @1
    @41
    @3
    cF
    cX
    filfbas
    adantr
    @10
    @13
    @0
    wcel
    #
    @42
    @10
    cJ
    cX
    ctopon
    cfv
    wcel
    #
    @11
    cX
    wss
    @11
    c0
    wne
    #
    @43
    @10
    @29
    cX
    @27
    wceq
    @44
    @30
    @33
    cX
    cJ
    istopon
    sylanbrc
    #
    @10
    cA
    cX
    @10
    cA
    @27
    cX
    @3
    cA
    @27
    wcel
    @1
    cA
    cF
    cJ
    @27
    @31
    fclselbas
    adantl
    @33
    eleqtrrd
    #
    snssd
    @3
    @45
    @1
    cA
    @2
    snnzg
    adantl
    @11
    cJ
    cX
    neifil
    syl3anc
    @13
    cX
    filfbas
    syl
    vx
    vy
    cF
    @13
    cX
    cX
    fbunfip
    syl2anc
    mpbird
    @1
    @22
    @24
    @25
    @26
    w3a
    wb
    #
    @3
    @1
    cX
    cF
    wcel
    @48
    cF
    cX
    filtop
    @14
    cF
    cX
    fsubbas
    syl
    adantr
    mpbir3and
    #
    @15
    cX
    fgcl
    syl
    #
    @10
    cF
    @15
    @16
    @10
    cF
    @13
    @15
    @1
    @14
    @15
    wss
    #
    @3
    @1
    @14
    cvv
    wcel
    #
    @51
    @1
    @13
    cvv
    wcel
    @52
    @11
    @12
    fvex
    cF
    @13
    @0
    cvv
    unexg
    mpan2
    @14
    cvv
    ssfii
    syl
    adantr
    #
    unssad
    @10
    @22
    @15
    @16
    wss
    @49
    @15
    cX
    ssfg
    syl
    #
    sstrd
    @10
    @20
    cA
    cX
    wcel
    #
    @13
    @16
    wss
    #
    @47
    @10
    @13
    @15
    @16
    @10
    cF
    @13
    @15
    @53
    unssbd
    @54
    sstrd
    @10
    @44
    @17
    @20
    @55
    @56
    wa
    wb
    @46
    @50
    cA
    @16
    cJ
    cX
    elflim
    syl2anc
    mpbir2and
    @8
    @18
    @20
    wa
    vg
    @16
    @0
    @4
    @16
    wceq
    #
    @5
    @18
    @7
    @20
    @4
    @16
    cF
    sseq2
    @57
    @6
    @19
    cA
    @4
    @16
    cJ
    cflim
    oveq2
    eleq2d
    anbi12d
    rspcev
    syl12anc
    ex
    @1
    @8
    @3
    vg
    @0
    @1
    @4
    @0
    wcel
    #
    @8
    wa
    #
    wa
    #
    cJ
    @4
    cfcls
    co
    #
    @2
    cA
    @60
    @44
    @1
    @5
    @61
    @2
    wss
    @60
    @44
    @58
    @1
    @58
    @8
    simprl
    @60
    @7
    @44
    @58
    wb
    @1
    @58
    @5
    @7
    simprrr
    #
    cA
    @4
    cJ
    cX
    flimtopon
    syl
    mpbird
    @1
    @59
    simpl
    @1
    @58
    @5
    @7
    simprrl
    cF
    @4
    cJ
    cX
    fclsss2
    syl3anc
    @60
    @6
    @61
    cA
    @4
    cJ
    flimfcls
    @62
    sseldi
    sseldd
    rexlimdvaa
    impbid
end
