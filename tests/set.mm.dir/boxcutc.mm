include "wcel.mm"
include "wss.mm"
include "wral.mm"
include "wa.mm"
include "cixp.mm"
include "cv.mm"
include "wceq.mm"
include "cif.mm"
include "cdif.mm"
include "eldifi.mm"
include "adantl.mm"
include "sseq1.mm"
include "difss.mm"
include "ssid.mm"
include "keephyp.mm"
include "rgenw.mm"
include "ss2ixp.mm"
include "mp1i.mm"
include "sselda.mm"
include "wn.mm"
include "wfn.mm"
include "cfv.mm"
include "ixpfn.mm"
include "biantrurd.mm"
include "vex.mm"
include "elixp.mm"
include "syl6rbbr.mm"
include "notbid.mm"
include "wrex.mm"
include "rexnal.mm"
include "csb.mm"
include "eleq2.mm"
include "simpl.mm"
include "simprbi.mm"
include "nfv.mm"
include "nfcsb1v.mm"
include "nfel2.mm"
include "weq.mm"
include "fveq2.mm"
include "csbeq1a.mm"
include "eleq12d.mm"
include "cbvral.mm"
include "sylib.mm"
include "csbeq1.mm"
include "rspcva.mm"
include "syl2an.mm"
include "neldif.mm"
include "sylan.mm"
include "adantr.mm"
include "syl5ibrcom.mm"
include "imp.mm"
include "ad2antlr.mm"
include "r19.21bi.mm"
include "ifbothda.mm"
include "ralrimiva.mm"
include "dfral2.mm"
include "ex.mm"
include "con4d.mm"
include "difeq12d.mm"
include "simpll.mm"
include "iftrue.mm"
include "eqtrd.mm"
include "eldifbd.mm"
include "rspcev.mm"
include "syl2an2r.mm"
include "impbida.mm"
include "nfif.mm"
include "nfn.mm"
include "eqeq1.mm"
include "ifbieq12d.mm"
include "cbvrex.mm"
include "nfdif.mm"
include "3bitr4g.mm"
include "syl5bbr.mm"
include "bitrd.mm"
include "wb.mm"
include "ibar.mm"
include "3bitr3d.mm"
include "eldif.mm"
include "eqrdav.mm"

theorem boxcutc
  let cA: class A
  let cB: class B
  let cC: class C
  let vk: setvar k
  let cX: class X
  let vl: setvar l
  let vm: setvar m
  let vz: setvar z

  disjoint A k
  disjoint X k
  disjoint A l
  disjoint A m
  disjoint A z
  disjoint k l
  disjoint k m
  disjoint k z
  disjoint l m
  disjoint l z
  disjoint m z
  disjoint B l
  disjoint B m
  disjoint B z
  disjoint C l
  disjoint C m
  disjoint C z
  disjoint X l
  disjoint X m
  disjoint X z
  assert |- ( ( X e. A /\ A. k e. A C C_ B ) -> ( X_ k e. A B \ X_ k e. A if ( k = X , C , B ) ) = X_ k e. A if ( k = X , ( B \ C ) , B ) )

  proof
    cX
    cA
    wcel
    #
    cC
    cB
    wss
    vk
    cA
    wral
    #
    wa
    #
    vz
    vk
    cA
    cB
    cixp
    #
    vk
    cA
    vk
    cv
    #
    cX
    wceq
    #
    cC
    cB
    cif
    #
    cixp
    #
    cdif
    #
    vk
    cA
    @5
    cB
    cC
    cdif
    #
    cB
    cif
    #
    cixp
    #
    @3
    vz
    cv
    #
    @8
    wcel
    #
    @12
    @3
    wcel
    #
    @2
    @12
    @3
    @7
    eldifi
    adantl
    @2
    @11
    @3
    @12
    @10
    cB
    wss
    #
    vk
    cA
    wral
    @11
    @3
    wss
    @2
    @15
    vk
    cA
    @5
    @9
    cB
    wss
    cB
    cB
    wss
    @15
    @9
    cB
    @9
    @10
    cB
    sseq1
    cB
    @10
    cB
    sseq1
    cB
    cC
    difss
    cB
    ssid
    keephyp
    rgenw
    vk
    cA
    @10
    cB
    ss2ixp
    mp1i
    sselda
    @2
    @14
    wa
    #
    @14
    @12
    @7
    wcel
    #
    wn
    #
    wa
    #
    @12
    cA
    wfn
    #
    @4
    @12
    cfv
    #
    @10
    wcel
    #
    vk
    cA
    wral
    #
    wa
    #
    @13
    @12
    @11
    wcel
    @16
    @18
    @23
    @19
    @24
    @16
    @18
    @21
    @6
    wcel
    #
    vk
    cA
    wral
    #
    wn
    #
    @23
    @16
    @17
    @26
    @16
    @26
    @20
    @26
    wa
    @17
    @16
    @20
    @26
    @14
    @20
    @2
    vk
    cA
    cB
    @12
    ixpfn
    adantl
    #
    biantrurd
    vk
    cA
    @6
    @12
    vz
    vex
    #
    elixp
    syl6rbbr
    notbid
    @27
    @25
    wn
    #
    vk
    cA
    wrex
    #
    @16
    @23
    @25
    vk
    cA
    rexnal
    @16
    vl
    cv
    #
    @12
    cfv
    #
    @32
    cX
    wceq
    #
    vk
    @32
    cC
    csb
    #
    vk
    @32
    cB
    csb
    #
    cif
    #
    wcel
    #
    wn
    #
    vl
    cA
    wrex
    #
    vm
    cv
    #
    @12
    cfv
    #
    @41
    cX
    wceq
    #
    vk
    @41
    cB
    csb
    #
    vk
    @41
    cC
    csb
    #
    cdif
    #
    @44
    cif
    #
    wcel
    #
    vm
    cA
    wral
    #
    @31
    @23
    @16
    @40
    @49
    @16
    @40
    wa
    #
    @48
    vm
    cA
    @43
    @42
    @46
    wcel
    #
    @42
    @44
    wcel
    #
    @48
    @50
    @41
    cA
    wcel
    #
    wa
    #
    @46
    @44
    @46
    @47
    @42
    eleq2
    @44
    @47
    @42
    eleq2
    @54
    @43
    @51
    @54
    @51
    @43
    cX
    @12
    cfv
    #
    vk
    cX
    cB
    csb
    #
    vk
    cX
    cC
    csb
    #
    cdif
    #
    wcel
    #
    @50
    @59
    @53
    @16
    @40
    @59
    @16
    @59
    @40
    @16
    @59
    wn
    #
    @40
    wn
    #
    @16
    @60
    wa
    #
    @38
    vl
    cA
    wral
    @61
    @62
    @38
    vl
    cA
    @34
    @33
    @35
    wcel
    #
    @33
    @36
    wcel
    #
    @38
    @62
    @32
    cA
    wcel
    #
    wa
    #
    @35
    @36
    @35
    @37
    @33
    eleq2
    @36
    @37
    @33
    eleq2
    @66
    @34
    @63
    @66
    @63
    @34
    @55
    @57
    wcel
    #
    @62
    @67
    @65
    @16
    @55
    @56
    wcel
    #
    @60
    @67
    @2
    @0
    @64
    vl
    cA
    wral
    #
    @68
    @14
    @0
    @1
    simpl
    @14
    @21
    cB
    wcel
    #
    vk
    cA
    wral
    #
    @69
    @14
    @20
    @71
    vk
    cA
    cB
    @12
    @29
    elixp
    simprbi
    #
    @70
    @64
    vk
    vl
    cA
    @70
    vl
    nfv
    vk
    @33
    @36
    vk
    @32
    cB
    nfcsb1v
    #
    nfel2
    vk
    vl
    weq
    #
    @21
    @33
    cB
    @36
    @4
    @32
    @12
    fveq2
    #
    vk
    @32
    cB
    csbeq1a
    #
    eleq12d
    cbvral
    sylib
    #
    @64
    @68
    vl
    cX
    cA
    @34
    @33
    @55
    @36
    @56
    @32
    cX
    @12
    fveq2
    #
    vk
    @32
    cX
    cB
    csbeq1
    eleq12d
    rspcva
    syl2an
    @55
    @56
    @57
    neldif
    sylan
    adantr
    @34
    @33
    @55
    @35
    @57
    @78
    vk
    @32
    cX
    cC
    csbeq1
    #
    eleq12d
    syl5ibrcom
    imp
    @66
    @64
    @34
    wn
    @62
    @64
    vl
    cA
    @14
    @69
    @2
    @60
    @77
    ad2antlr
    r19.21bi
    adantr
    ifbothda
    ralrimiva
    @38
    vl
    cA
    dfral2
    sylib
    ex
    con4d
    imp
    adantr
    @43
    @42
    @55
    @46
    @58
    @41
    cX
    @12
    fveq2
    #
    @43
    @44
    @56
    @45
    @57
    vk
    @41
    cX
    cB
    csbeq1
    vk
    @41
    cX
    cC
    csbeq1
    difeq12d
    #
    eleq12d
    syl5ibrcom
    imp
    @54
    @52
    @43
    wn
    @50
    @52
    vm
    cA
    @14
    @52
    vm
    cA
    wral
    #
    @2
    @40
    @14
    @71
    @82
    @72
    @70
    @52
    vk
    vm
    cA
    @70
    vm
    nfv
    vk
    @42
    @44
    vk
    @41
    cB
    nfcsb1v
    #
    nfel2
    vk
    vm
    weq
    #
    @21
    @42
    cB
    @44
    @4
    @41
    @12
    fveq2
    #
    vk
    @41
    cB
    csbeq1a
    #
    eleq12d
    cbvral
    sylib
    ad2antlr
    r19.21bi
    adantr
    ifbothda
    ralrimiva
    @16
    @0
    @49
    @67
    wn
    #
    @40
    @0
    @1
    @14
    simpll
    #
    @16
    @49
    wa
    @55
    @56
    @57
    @16
    @0
    @49
    @59
    @88
    @48
    @59
    vm
    cX
    cA
    @43
    @42
    @55
    @47
    @58
    @80
    @43
    @47
    @46
    @58
    @43
    @46
    @44
    iftrue
    @81
    eqtrd
    eleq12d
    rspcva
    sylan
    eldifbd
    @39
    @87
    vl
    cX
    cA
    @34
    @38
    @67
    @34
    @33
    @55
    @37
    @57
    @78
    @34
    @37
    @35
    @57
    @34
    @35
    @36
    iftrue
    @79
    eqtrd
    eleq12d
    notbid
    rspcev
    syl2an2r
    impbida
    @30
    @39
    vk
    vl
    cA
    @30
    vl
    nfv
    @38
    vk
    vk
    @33
    @37
    @34
    vk
    @35
    @36
    @34
    vk
    nfv
    vk
    @32
    cC
    nfcsb1v
    @73
    nfif
    nfel2
    nfn
    @74
    @25
    @38
    @74
    @21
    @33
    @6
    @37
    @75
    @74
    @5
    @34
    cC
    cB
    @35
    @36
    @4
    @32
    cX
    eqeq1
    vk
    @32
    cC
    csbeq1a
    @76
    ifbieq12d
    eleq12d
    notbid
    cbvrex
    @22
    @48
    vk
    vm
    cA
    @22
    vm
    nfv
    vk
    @42
    @47
    @43
    vk
    @46
    @44
    @43
    vk
    nfv
    vk
    @44
    @45
    @83
    vk
    @41
    cC
    nfcsb1v
    nfdif
    @83
    nfif
    nfel2
    @84
    @21
    @42
    @10
    @47
    @85
    @84
    @5
    @43
    @9
    cB
    @46
    @44
    @4
    @41
    cX
    eqeq1
    @84
    cB
    @44
    cC
    @45
    @86
    vk
    @41
    cC
    csbeq1a
    difeq12d
    @86
    ifbieq12d
    eleq12d
    cbvral
    3bitr4g
    syl5bbr
    bitrd
    @14
    @18
    @19
    wb
    @2
    @14
    @18
    ibar
    adantl
    @16
    @20
    @23
    @28
    biantrurd
    3bitr3d
    @12
    @3
    @7
    eldif
    vk
    cA
    @10
    @12
    @29
    elixp
    3bitr4g
    eqrdav
end
