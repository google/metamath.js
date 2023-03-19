include "chlt.mm"
include "wcel.mm"
include "wss.mm"
include "w3a.mm"
include "cfv.mm"
include "wceq.mm"
include "club.mm"
include "cpmap.mm"
include "cin.mm"
include "eqcom.mm"
include "eqid.mm"
include "2polvalN.mm"
include "3adant2.mm"
include "eqeq2d.mm"
include "biimpd.mm"
include "syl5bi.mm"
include "wa.mm"
include "coc.mm"
include "cmee.mm"
include "co.mm"
include "coml.mm"
include "cbs.mm"
include "cple.mm"
include "wbr.mm"
include "simpl1.mm"
include "hloml.mm"
include "syl.mm"
include "ccla.mm"
include "hlclat.mm"
include "simpl2.mm"
include "atssbase.mm"
include "syl6ss.mm"
include "clatlubcl.mm"
include "syl2anc.mm"
include "simpl3.mm"
include "3jca.mm"
include "simprl.mm"
include "lubss.mm"
include "syl3anc.mm"
include "omllaw4.mm"
include "sylc.mm"
include "fveq2d.mm"
include "polval2N.mm"
include "simprr.mm"
include "ineq12d.mm"
include "cops.mm"
include "hlop.mm"
include "opoccl.mm"
include "pmapmeet.mm"
include "eqtr4d.mm"
include "clat.mm"
include "hllat.mm"
include "latmcl.mm"
include "polpmapN.mm"
include "eqtrd.mm"
include "3eqtr4d.mm"
include "ex.mm"
include "sylan2d.mm"

theorem poml4N
  let cA: class A
  let cK: class K
  let c.pe: class ._|_
  let cX: class X
  let cY: class Y
  assume poml4.a: |- A = ( Atoms ` K )
  assume poml4.p: |- ._|_ = ( _|_P ` K )


  assert |- ( ( K e. HL /\ X C_ A /\ Y C_ A ) -> ( ( X C_ Y /\ ( ._|_ ` ( ._|_ ` Y ) ) = Y ) -> ( ( ._|_ ` ( ( ._|_ ` X ) i^i Y ) ) i^i Y ) = ( ._|_ ` ( ._|_ ` X ) ) ) )

  proof
    cK
    chlt
    wcel
    #
    cX
    cA
    wss
    #
    cY
    cA
    wss
    #
    w3a
    #
    cY
    c.pe
    cfv
    c.pe
    cfv
    #
    cY
    wceq
    #
    cY
    cY
    cK
    club
    cfv
    #
    cfv
    #
    cK
    cpmap
    cfv
    #
    cfv
    #
    wceq
    #
    cX
    cY
    wss
    #
    cX
    c.pe
    cfv
    #
    cY
    cin
    #
    c.pe
    cfv
    #
    cY
    cin
    #
    @12
    c.pe
    cfv
    #
    wceq
    #
    @5
    cY
    @4
    wceq
    #
    @3
    @10
    @4
    cY
    eqcom
    @3
    @18
    @10
    @3
    @4
    @9
    cY
    @0
    @2
    @4
    @9
    wceq
    @1
    cA
    @6
    cK
    @8
    c.pe
    cY
    @6
    eqid
    #
    poml4.a
    @8
    eqid
    #
    poml4.p
    2polvalN
    3adant2
    eqeq2d
    biimpd
    syl5bi
    @3
    @11
    @10
    wa
    #
    @17
    @3
    @21
    wa
    #
    cX
    @6
    cfv
    #
    cK
    coc
    cfv
    #
    cfv
    #
    @7
    cK
    cmee
    cfv
    #
    co
    #
    @24
    cfv
    #
    @7
    @26
    co
    #
    @8
    cfv
    #
    @23
    @8
    cfv
    #
    @15
    @16
    @22
    @29
    @23
    @8
    @22
    cK
    coml
    wcel
    #
    @23
    cK
    cbs
    cfv
    #
    wcel
    #
    @7
    @33
    wcel
    #
    w3a
    @23
    @7
    cK
    cple
    cfv
    #
    wbr
    #
    @29
    @23
    wceq
    @22
    @32
    @34
    @35
    @22
    @0
    @32
    @0
    @1
    @2
    @21
    simpl1
    #
    cK
    hloml
    syl
    @22
    cK
    ccla
    wcel
    #
    cX
    @33
    wss
    @34
    @22
    @0
    @39
    @38
    cK
    hlclat
    syl
    #
    @22
    cX
    cA
    @33
    @0
    @1
    @2
    @21
    simpl2
    #
    cA
    @33
    cK
    @33
    eqid
    #
    poml4.a
    atssbase
    #
    syl6ss
    @33
    cX
    @6
    cK
    @42
    @19
    clatlubcl
    syl2anc
    #
    @22
    @39
    cY
    @33
    wss
    #
    @35
    @40
    @22
    cY
    cA
    @33
    @0
    @1
    @2
    @21
    simpl3
    @43
    syl6ss
    #
    @33
    cY
    @6
    cK
    @42
    @19
    clatlubcl
    syl2anc
    #
    3jca
    @22
    @39
    @45
    @11
    @37
    @40
    @46
    @3
    @11
    @10
    simprl
    @33
    cX
    cY
    @6
    cK
    @36
    @42
    @36
    eqid
    #
    @19
    lubss
    syl3anc
    @33
    cK
    @36
    @26
    @24
    @23
    @7
    @42
    @48
    @26
    eqid
    #
    @24
    eqid
    #
    omllaw4
    sylc
    fveq2d
    @22
    @15
    @28
    @8
    cfv
    #
    @9
    cin
    #
    @30
    @22
    @14
    @51
    cY
    @9
    @22
    @14
    @27
    @8
    cfv
    #
    c.pe
    cfv
    #
    @51
    @22
    @13
    @53
    c.pe
    @22
    @13
    @25
    @8
    cfv
    #
    @9
    cin
    #
    @53
    @22
    @12
    @55
    cY
    @9
    @22
    @0
    @1
    @12
    @55
    wceq
    @38
    @41
    cA
    c.pe
    @6
    cK
    @8
    @24
    cX
    @19
    @50
    poml4.a
    @20
    poml4.p
    polval2N
    syl2anc
    @3
    @11
    @10
    simprr
    #
    ineq12d
    @22
    @0
    @25
    @33
    wcel
    #
    @35
    @53
    @56
    wceq
    @38
    @22
    cK
    cops
    wcel
    #
    @34
    @58
    @22
    @0
    @59
    @38
    cK
    hlop
    syl
    #
    @44
    @33
    cK
    @24
    @23
    @42
    @50
    opoccl
    syl2anc
    #
    @47
    cA
    @33
    @8
    cK
    @26
    @25
    @7
    @42
    @49
    poml4.a
    @20
    pmapmeet
    syl3anc
    eqtr4d
    fveq2d
    @22
    @0
    @27
    @33
    wcel
    #
    @54
    @51
    wceq
    @38
    @22
    cK
    clat
    wcel
    #
    @58
    @35
    @62
    @22
    @0
    @63
    @38
    cK
    hllat
    syl
    @61
    @47
    @33
    cK
    @26
    @25
    @7
    @42
    @49
    latmcl
    syl3anc
    #
    @33
    c.pe
    cK
    @8
    @24
    @27
    @42
    @50
    @20
    poml4.p
    polpmapN
    syl2anc
    eqtrd
    @57
    ineq12d
    @22
    @0
    @28
    @33
    wcel
    #
    @35
    @30
    @52
    wceq
    @38
    @22
    @59
    @62
    @65
    @60
    @64
    @33
    cK
    @24
    @27
    @42
    @50
    opoccl
    syl2anc
    @47
    cA
    @33
    @8
    cK
    @26
    @28
    @7
    @42
    @49
    poml4.a
    @20
    pmapmeet
    syl3anc
    eqtr4d
    @22
    @0
    @1
    @16
    @31
    wceq
    @38
    @41
    cA
    @6
    cK
    @8
    c.pe
    cX
    @19
    poml4.a
    @20
    poml4.p
    2polvalN
    syl2anc
    3eqtr4d
    ex
    sylan2d
end
