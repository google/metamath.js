include "clmod.mm"
include "wcel.mm"
include "wa.mm"
include "cplusg.mm"
include "cfv.mm"
include "cv.mm"
include "co.mm"
include "wceq.mm"
include "wrex.mm"
include "cab.mm"
include "csca.mm"
include "a1i.mm"
include "cbs.mm"
include "eqidd.mm"
include "cvsca.mm"
include "clss.mm"
include "wi.mm"
include "lmodvscl.mm"
include "3expa.mm"
include "an32s.mm"
include "eleq1a.mm"
include "syl.mm"
include "rexlimdva.mm"
include "abssdv.mm"
include "c0g.mm"
include "c0.mm"
include "wne.mm"
include "eqid.mm"
include "lmod0cl.mm"
include "adantr.mm"
include "nfcv.mm"
include "nfre1.mm"
include "nfab.mm"
include "nfne.mm"
include "biidd.mm"
include "ovex.mm"
include "elabrex.mm"
include "ne0i.mm"
include "vtoclgaf.mm"
include "w3a.mm"
include "vex.mm"
include "eqeq1.mm"
include "rexbidv.mm"
include "elab.mm"
include "oveq1.mm"
include "eqeq2d.mm"
include "cbvrexv.mm"
include "bitri.mm"
include "anbi12i.mm"
include "reeanv.mm"
include "bitr4i.mm"
include "cmulr.mm"
include "simpll.mm"
include "simprr.mm"
include "simprll.mm"
include "lmodmcl.mm"
include "syl3anc.mm"
include "simprlr.mm"
include "lmodacl.mm"
include "simplr.mm"
include "lmodvsdir.mm"
include "syl13anc.mm"
include "lmodvsass.mm"
include "oveq1d.mm"
include "eqtr2d.mm"
include "rspcev.mm"
include "syl2anc.mm"
include "oveq2.mm"
include "oveq12.mm"
include "sylan.mm"
include "eqeq1d.mm"
include "syl5ibrcom.mm"
include "expr.mm"
include "com23.mm"
include "rexlimdvva.mm"
include "syl5bi.mm"
include "expcomd.mm"
include "com24.mm"
include "3imp2.mm"
include "sylibr.mm"
include "islssd.mm"

theorem lss1d
  let vv: setvar v
  let cS: class S
  let c.x: class .x.
  let vk: setvar k
  let cF: class F
  let cK: class K
  let cV: class V
  let cW: class W
  let cX: class X
  let va: setvar a
  let vb: setvar b
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume lss1d.v: |- V = ( Base ` W )
  assume lss1d.f: |- F = ( Scalar ` W )
  assume lss1d.t: |- .x. = ( .s ` W )
  assume lss1d.k: |- K = ( Base ` F )
  assume lss1d.s: |- S = ( LSubSp ` W )

  disjoint k v
  disjoint K k
  disjoint K v
  disjoint .x. k
  disjoint .x. v
  disjoint V k
  disjoint V v
  disjoint F k
  disjoint W k
  disjoint W v
  disjoint X k
  disjoint X v
  disjoint a b
  disjoint a k
  disjoint a v
  disjoint a x
  disjoint a y
  disjoint a z
  disjoint K a
  disjoint b k
  disjoint b v
  disjoint b x
  disjoint b y
  disjoint b z
  disjoint K b
  disjoint k x
  disjoint k y
  disjoint k z
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint x y
  disjoint x z
  disjoint K x
  disjoint y z
  disjoint K y
  disjoint K z
  disjoint .x. a
  disjoint .x. b
  disjoint .x. x
  disjoint .x. y
  disjoint .x. z
  disjoint V a
  disjoint V b
  disjoint V x
  disjoint V y
  disjoint V z
  disjoint F x
  disjoint W a
  disjoint W b
  disjoint W x
  disjoint W y
  disjoint W z
  disjoint X a
  disjoint X b
  disjoint X x
  disjoint X y
  disjoint X z
  assert |- ( ( W e. LMod /\ X e. V ) -> { v | E. k e. K v = ( k .x. X ) } e. S )

  proof
    cW
    clmod
    wcel
    #
    cX
    cV
    wcel
    #
    wa
    #
    vx
    cK
    cW
    cplusg
    cfv
    #
    cS
    c.x
    vv
    cv
    #
    vk
    cv
    #
    cX
    c.x
    co
    #
    wceq
    #
    vk
    cK
    wrex
    #
    vv
    cab
    #
    cF
    cV
    cW
    va
    vb
    cF
    cW
    csca
    cfv
    wceq
    @2
    lss1d.f
    a1i
    cK
    cF
    cbs
    cfv
    wceq
    @2
    lss1d.k
    a1i
    cV
    cW
    cbs
    cfv
    wceq
    @2
    lss1d.v
    a1i
    @2
    @3
    eqidd
    c.x
    cW
    cvsca
    cfv
    wceq
    @2
    lss1d.t
    a1i
    cS
    cW
    clss
    cfv
    wceq
    @2
    lss1d.s
    a1i
    @2
    @8
    vv
    cV
    @2
    @7
    @4
    cV
    wcel
    #
    vk
    cK
    @2
    @5
    cK
    wcel
    #
    wa
    @6
    cV
    wcel
    #
    @7
    @10
    wi
    @0
    @11
    @1
    @12
    @0
    @11
    @1
    @12
    @5
    c.x
    cF
    cK
    cV
    cW
    cX
    lss1d.v
    lss1d.f
    lss1d.t
    lss1d.k
    lmodvscl
    3expa
    an32s
    @6
    cV
    @4
    eleq1a
    syl
    rexlimdva
    abssdv
    @2
    cF
    c0g
    cfv
    #
    cK
    wcel
    #
    @9
    c0
    wne
    #
    @0
    @14
    @1
    cF
    cK
    cW
    @13
    lss1d.f
    lss1d.k
    @13
    eqid
    lmod0cl
    adantr
    @15
    @15
    vk
    @13
    cK
    vk
    @13
    nfcv
    vk
    @9
    c0
    @8
    vk
    vv
    @7
    vk
    cK
    nfre1
    nfab
    vk
    c0
    nfcv
    nfne
    @5
    @13
    wceq
    @15
    biidd
    @11
    @6
    @9
    wcel
    @15
    vk
    vv
    cK
    @6
    @5
    cX
    c.x
    ovex
    elabrex
    @9
    @6
    ne0i
    syl
    vtoclgaf
    syl
    @2
    vx
    cv
    #
    cK
    wcel
    #
    va
    cv
    #
    @9
    wcel
    #
    vb
    cv
    #
    @9
    wcel
    #
    w3a
    wa
    @16
    @18
    c.x
    co
    #
    @20
    @3
    co
    #
    @6
    wceq
    #
    vk
    cK
    wrex
    #
    @23
    @9
    wcel
    @2
    @17
    @19
    @21
    @25
    @2
    @21
    @19
    @17
    @25
    @2
    @19
    @21
    @17
    @25
    wi
    #
    @19
    @21
    wa
    #
    @18
    vy
    cv
    #
    cX
    c.x
    co
    #
    wceq
    #
    @20
    vz
    cv
    #
    cX
    c.x
    co
    #
    wceq
    #
    wa
    #
    vz
    cK
    wrex
    vy
    cK
    wrex
    #
    @2
    @26
    @27
    @30
    vy
    cK
    wrex
    #
    @33
    vz
    cK
    wrex
    #
    wa
    @35
    @19
    @36
    @21
    @37
    @19
    @18
    @6
    wceq
    #
    vk
    cK
    wrex
    #
    @36
    @8
    @39
    vv
    @18
    va
    vex
    @4
    @18
    wceq
    @7
    @38
    vk
    cK
    @4
    @18
    @6
    eqeq1
    rexbidv
    elab
    @38
    @30
    vk
    vy
    cK
    @5
    @28
    wceq
    @6
    @29
    @18
    @5
    @28
    cX
    c.x
    oveq1
    eqeq2d
    cbvrexv
    bitri
    @21
    @20
    @6
    wceq
    #
    vk
    cK
    wrex
    #
    @37
    @8
    @41
    vv
    @20
    vb
    vex
    @4
    @20
    wceq
    @7
    @40
    vk
    cK
    @4
    @20
    @6
    eqeq1
    rexbidv
    elab
    @40
    @33
    vk
    vz
    cK
    @5
    @31
    wceq
    @6
    @32
    @20
    @5
    @31
    cX
    c.x
    oveq1
    eqeq2d
    cbvrexv
    bitri
    anbi12i
    @30
    @33
    vy
    vz
    cK
    cK
    reeanv
    bitr4i
    @2
    @34
    @26
    vy
    vz
    cK
    cK
    @2
    @28
    cK
    wcel
    #
    @31
    cK
    wcel
    #
    wa
    #
    wa
    @17
    @34
    @25
    @2
    @44
    @17
    @34
    @25
    wi
    @2
    @44
    @17
    wa
    #
    wa
    #
    @25
    @34
    @16
    @29
    c.x
    co
    #
    @32
    @3
    co
    #
    @6
    wceq
    #
    vk
    cK
    wrex
    #
    @46
    @16
    @28
    cF
    cmulr
    cfv
    #
    co
    #
    @31
    cF
    cplusg
    cfv
    #
    co
    #
    cK
    wcel
    #
    @48
    @54
    cX
    c.x
    co
    #
    wceq
    #
    @50
    @46
    @0
    @52
    cK
    wcel
    #
    @43
    @55
    @0
    @1
    @45
    simpll
    #
    @46
    @0
    @17
    @42
    @58
    @59
    @2
    @44
    @17
    simprr
    #
    @2
    @42
    @43
    @17
    simprll
    #
    @51
    cF
    cK
    cW
    @16
    @28
    lss1d.f
    lss1d.k
    @51
    eqid
    #
    lmodmcl
    syl3anc
    #
    @2
    @42
    @43
    @17
    simprlr
    #
    @53
    cF
    cK
    cW
    @52
    @31
    lss1d.f
    lss1d.k
    @53
    eqid
    #
    lmodacl
    syl3anc
    @46
    @56
    @52
    cX
    c.x
    co
    #
    @32
    @3
    co
    #
    @48
    @46
    @0
    @58
    @43
    @1
    @56
    @67
    wceq
    @59
    @63
    @64
    @0
    @1
    @45
    simplr
    #
    @3
    @53
    @52
    @31
    c.x
    cF
    cK
    cV
    cW
    cX
    lss1d.v
    @3
    eqid
    lss1d.f
    lss1d.t
    lss1d.k
    @65
    lmodvsdir
    syl13anc
    @46
    @66
    @47
    @32
    @3
    @46
    @0
    @17
    @42
    @1
    @66
    @47
    wceq
    @59
    @60
    @61
    @68
    @16
    @28
    c.x
    @51
    cF
    cK
    cV
    cW
    cX
    lss1d.v
    lss1d.f
    lss1d.t
    lss1d.k
    @62
    lmodvsass
    syl13anc
    oveq1d
    eqtr2d
    @49
    @57
    vk
    @54
    cK
    @5
    @54
    wceq
    @6
    @56
    @48
    @5
    @54
    cX
    c.x
    oveq1
    eqeq2d
    rspcev
    syl2anc
    @34
    @24
    @49
    vk
    cK
    @34
    @23
    @48
    @6
    @30
    @22
    @47
    wceq
    @33
    @23
    @48
    wceq
    @18
    @29
    @16
    c.x
    oveq2
    @22
    @47
    @20
    @32
    @3
    oveq12
    sylan
    eqeq1d
    rexbidv
    syl5ibrcom
    expr
    com23
    rexlimdvva
    syl5bi
    expcomd
    com24
    3imp2
    @8
    @25
    vv
    @23
    @22
    @20
    @3
    ovex
    @4
    @23
    wceq
    @7
    @24
    vk
    cK
    @4
    @23
    @6
    eqeq1
    rexbidv
    elab
    sylibr
    islssd
end
