include "wss.mm"
include "chlt.mm"
include "wcel.mm"
include "cfv.mm"
include "cv.mm"
include "crab.mm"
include "cin.mm"
include "dfin5.mm"
include "wceq.mm"
include "sseqin2.mm"
include "biimpi.mm"
include "syl5reqr.mm"
include "fveq2d.mm"
include "cple.mm"
include "wbr.mm"
include "wral.mm"
include "wi.mm"
include "wa.mm"
include "crio.mm"
include "eqid.mm"
include "biid.mm"
include "id.mm"
include "ssrab2.mm"
include "a1i.mm"
include "glbval.mm"
include "cops.mm"
include "wreu.mm"
include "hlop.mm"
include "ccla.mm"
include "hlclat.mm"
include "clatglbcl.mm"
include "sylancl.mm"
include "eqeltrrd.mm"
include "cbs.mm"
include "cvv.mm"
include "fvex.mm"
include "eqeltri.mm"
include "riotaclbBAD.mm"
include "sylibr.mm"
include "breq1.mm"
include "ralbidv.mm"
include "breq2.mm"
include "imbi2d.mm"
include "anbi12d.mm"
include "riotaocN.mm"
include "syl2anc.mm"
include "ad2antrr.mm"
include "opoccl.mm"
include "sylancom.mm"
include "wrex.mm"
include "opococ.mm"
include "eqcomd.mm"
include "fveq2.mm"
include "eqeq2d.mm"
include "rspcev.mm"
include "wb.mm"
include "eleq1.mm"
include "imbi12d.mm"
include "adantl.mm"
include "ralxfrd.mm"
include "simpr.mm"
include "simplr.mm"
include "oplecon3b.mm"
include "syl3anc.mm"
include "ralbidva.mm"
include "bitr4d.mm"
include "ralrab.mm"
include "weq.mm"
include "eleq1d.mm"
include "3bitr4g.mm"
include "ad3antrrr.mm"
include "riotabidva.mm"
include "simpl.mm"
include "lubval.mm"
include "mpan2.mm"
include "eqtr4d.mm"
include "3eqtrd.mm"
include "sylan9eqr.mm"

theorem glbconN
  let vx: setvar x
  let cB: class B
  let cS: class S
  let cU: class U
  let cG: class G
  let cK: class K
  let c.pe: class ._|_
  let vt: setvar t
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
  let vy: setvar y
  let vz: setvar z
  assume glbcon.b: |- B = ( Base ` K )
  assume glbcon.u: |- U = ( lub ` K )
  assume glbcon.g: |- G = ( glb ` K )
  assume glbcon.o: |- ._|_ = ( oc ` K )

  disjoint B x
  disjoint ._|_ x
  disjoint S x
  disjoint t u
  disjoint t v
  disjoint t w
  disjoint t x
  disjoint t y
  disjoint t z
  disjoint B t
  disjoint u v
  disjoint u w
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint B u
  disjoint v w
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint B v
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint B w
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint B y
  disjoint B z
  disjoint K t
  disjoint K u
  disjoint K v
  disjoint K w
  disjoint K y
  disjoint K z
  disjoint ._|_ t
  disjoint ._|_ u
  disjoint ._|_ v
  disjoint ._|_ w
  disjoint ._|_ y
  disjoint ._|_ z
  disjoint S t
  disjoint S u
  disjoint S v
  disjoint S w
  disjoint S y
  disjoint S z
  assert |- ( ( K e. HL /\ S C_ B ) -> ( G ` S ) = ( ._|_ ` ( U ` { x e. B | ( ._|_ ` x ) e. S } ) ) )

  proof
    cS
    cB
    wss
    #
    cK
    chlt
    wcel
    #
    cS
    cG
    cfv
    vx
    cv
    #
    cS
    wcel
    #
    vx
    cB
    crab
    #
    cG
    cfv
    #
    @2
    c.pe
    cfv
    #
    cS
    wcel
    #
    vx
    cB
    crab
    #
    cU
    cfv
    #
    c.pe
    cfv
    #
    @0
    cS
    @4
    cG
    @0
    @4
    cB
    cS
    cin
    #
    cS
    vx
    cB
    cS
    dfin5
    @0
    @11
    cS
    wceq
    cS
    cB
    sseqin2
    biimpi
    syl5reqr
    fveq2d
    @1
    @5
    vy
    cv
    #
    vz
    cv
    #
    cK
    cple
    cfv
    #
    wbr
    #
    vz
    @4
    wral
    #
    vw
    cv
    #
    @13
    @14
    wbr
    #
    vz
    @4
    wral
    #
    @17
    @12
    @14
    wbr
    #
    wi
    #
    vw
    cB
    wral
    #
    wa
    #
    vy
    cB
    crio
    #
    vv
    cv
    #
    c.pe
    cfv
    #
    @13
    @14
    wbr
    #
    vz
    @4
    wral
    #
    @19
    @17
    @26
    @14
    wbr
    #
    wi
    #
    vw
    cB
    wral
    #
    wa
    #
    vv
    cB
    crio
    #
    c.pe
    cfv
    #
    @10
    @1
    @23
    vy
    vz
    vw
    cB
    @4
    cG
    cK
    @14
    chlt
    glbcon.b
    @14
    eqid
    #
    glbcon.g
    @23
    biid
    @1
    id
    @4
    cB
    wss
    #
    @1
    @3
    vx
    cB
    ssrab2
    #
    a1i
    glbval
    #
    @1
    cK
    cops
    wcel
    #
    @23
    vy
    cB
    wreu
    #
    @24
    @34
    wceq
    cK
    hlop
    #
    @1
    @24
    cB
    wcel
    @40
    @1
    @5
    @24
    cB
    @38
    @1
    cK
    ccla
    wcel
    @36
    @5
    cB
    wcel
    cK
    hlclat
    @37
    cB
    @4
    cG
    cK
    glbcon.b
    glbcon.g
    clatglbcl
    sylancl
    eqeltrrd
    @23
    vy
    cB
    cB
    cK
    cbs
    cfv
    cvv
    glbcon.b
    cK
    cbs
    fvex
    eqeltri
    riotaclbBAD
    sylibr
    @23
    @32
    vy
    vv
    cB
    cK
    c.pe
    glbcon.b
    glbcon.o
    @12
    @26
    wceq
    #
    @16
    @28
    @22
    @31
    @42
    @15
    @27
    vz
    @4
    @12
    @26
    @13
    @14
    breq1
    ralbidv
    @42
    @21
    @30
    vw
    cB
    @42
    @20
    @29
    @19
    @12
    @26
    @17
    @14
    breq2
    imbi2d
    ralbidv
    anbi12d
    riotaocN
    syl2anc
    @1
    @33
    @9
    c.pe
    @1
    @33
    vu
    cv
    #
    @25
    @14
    wbr
    #
    vu
    @8
    wral
    #
    @43
    vt
    cv
    #
    @14
    wbr
    #
    vu
    @8
    wral
    #
    @25
    @46
    @14
    wbr
    #
    wi
    #
    vt
    cB
    wral
    #
    wa
    #
    vv
    cB
    crio
    #
    @9
    @1
    @32
    @52
    vv
    cB
    @1
    @25
    cB
    wcel
    #
    wa
    #
    @28
    @45
    @31
    @51
    @55
    @13
    cS
    wcel
    #
    @27
    wi
    #
    vz
    cB
    wral
    #
    @43
    c.pe
    cfv
    #
    cS
    wcel
    #
    @44
    wi
    #
    vu
    cB
    wral
    #
    @28
    @45
    @55
    @58
    @60
    @26
    @59
    @14
    wbr
    #
    wi
    #
    vu
    cB
    wral
    @62
    @55
    @57
    @64
    vz
    vu
    @59
    cB
    cB
    @55
    @43
    cB
    wcel
    #
    @39
    @59
    cB
    wcel
    #
    @1
    @39
    @54
    @65
    @41
    ad2antrr
    #
    cB
    cK
    c.pe
    @43
    glbcon.b
    glbcon.o
    opoccl
    #
    sylancom
    @55
    @13
    cB
    wcel
    #
    wa
    #
    @13
    c.pe
    cfv
    #
    cB
    wcel
    #
    @13
    @71
    c.pe
    cfv
    #
    wceq
    #
    @13
    @59
    wceq
    #
    vu
    cB
    wrex
    #
    @55
    @69
    @39
    @72
    @1
    @39
    @54
    @69
    @41
    ad2antrr
    #
    cB
    cK
    c.pe
    @13
    glbcon.b
    glbcon.o
    opoccl
    #
    sylancom
    @70
    @73
    @13
    @55
    @69
    @39
    @73
    @13
    wceq
    #
    @77
    cB
    cK
    c.pe
    @13
    glbcon.b
    glbcon.o
    opococ
    #
    sylancom
    eqcomd
    @75
    @74
    vu
    @71
    cB
    @43
    @71
    wceq
    @59
    @73
    @13
    @43
    @71
    c.pe
    fveq2
    eqeq2d
    rspcev
    #
    syl2anc
    @75
    @57
    @64
    wb
    @55
    @75
    @56
    @60
    @27
    @63
    @13
    @59
    cS
    eleq1
    #
    @13
    @59
    @26
    @14
    breq2
    imbi12d
    adantl
    ralxfrd
    @55
    @61
    @64
    vu
    cB
    @55
    @65
    wa
    #
    @44
    @63
    @60
    @83
    @39
    @65
    @54
    @44
    @63
    wb
    @67
    @55
    @65
    simpr
    @1
    @54
    @65
    simplr
    cB
    cK
    @14
    c.pe
    @43
    @25
    glbcon.b
    @35
    glbcon.o
    oplecon3b
    syl3anc
    imbi2d
    ralbidva
    bitr4d
    @3
    @56
    @27
    vz
    vx
    cB
    @2
    @13
    cS
    eleq1
    #
    ralrab
    @7
    @60
    @44
    vu
    vx
    cB
    vx
    vu
    weq
    @6
    @59
    cS
    @2
    @43
    c.pe
    fveq2
    eleq1d
    #
    ralrab
    3bitr4g
    @55
    @31
    @46
    c.pe
    cfv
    #
    @13
    @14
    wbr
    #
    vz
    @4
    wral
    #
    @86
    @26
    @14
    wbr
    #
    wi
    #
    vt
    cB
    wral
    @51
    @55
    @30
    @90
    vw
    vt
    @86
    cB
    cB
    @55
    @46
    cB
    wcel
    #
    @39
    @86
    cB
    wcel
    @1
    @39
    @54
    @91
    @41
    ad2antrr
    #
    cB
    cK
    c.pe
    @46
    glbcon.b
    glbcon.o
    opoccl
    sylancom
    @55
    @17
    cB
    wcel
    #
    wa
    #
    @17
    c.pe
    cfv
    #
    cB
    wcel
    #
    @17
    @95
    c.pe
    cfv
    #
    wceq
    #
    @17
    @86
    wceq
    #
    vt
    cB
    wrex
    @55
    @93
    @39
    @96
    @1
    @39
    @54
    @93
    @41
    ad2antrr
    #
    cB
    cK
    c.pe
    @17
    glbcon.b
    glbcon.o
    opoccl
    sylancom
    @94
    @97
    @17
    @55
    @93
    @39
    @97
    @17
    wceq
    @100
    cB
    cK
    c.pe
    @17
    glbcon.b
    glbcon.o
    opococ
    sylancom
    eqcomd
    @99
    @98
    vt
    @95
    cB
    @46
    @95
    wceq
    @86
    @97
    @17
    @46
    @95
    c.pe
    fveq2
    eqeq2d
    rspcev
    syl2anc
    @99
    @30
    @90
    wb
    @55
    @99
    @19
    @88
    @29
    @89
    @99
    @18
    @87
    vz
    @4
    @17
    @86
    @13
    @14
    breq1
    ralbidv
    @17
    @86
    @26
    @14
    breq1
    imbi12d
    adantl
    ralxfrd
    @55
    @50
    @90
    vt
    cB
    @55
    @91
    wa
    #
    @48
    @88
    @49
    @89
    @101
    @60
    @47
    wi
    #
    vu
    cB
    wral
    #
    @56
    @87
    wi
    #
    vz
    cB
    wral
    #
    @48
    @88
    @101
    @103
    @60
    @86
    @59
    @14
    wbr
    #
    wi
    #
    vu
    cB
    wral
    @105
    @101
    @102
    @107
    vu
    cB
    @101
    @65
    wa
    #
    @47
    @106
    @60
    @108
    @39
    @65
    @91
    @47
    @106
    wb
    @1
    @39
    @54
    @91
    @65
    @41
    ad3antrrr
    #
    @101
    @65
    simpr
    @55
    @91
    @65
    simplr
    cB
    cK
    @14
    c.pe
    @43
    @46
    glbcon.b
    @35
    glbcon.o
    oplecon3b
    syl3anc
    imbi2d
    ralbidva
    @101
    @104
    @107
    vz
    vu
    @59
    cB
    cB
    @101
    @65
    @39
    @66
    @109
    @68
    sylancom
    @101
    @69
    wa
    #
    @72
    @74
    @76
    @101
    @69
    @39
    @72
    @1
    @39
    @54
    @91
    @69
    @41
    ad3antrrr
    #
    @78
    sylancom
    @110
    @73
    @13
    @101
    @69
    @39
    @79
    @111
    @80
    sylancom
    eqcomd
    @81
    syl2anc
    @75
    @104
    @107
    wb
    @101
    @75
    @56
    @60
    @87
    @106
    @82
    @13
    @59
    @86
    @14
    breq2
    imbi12d
    adantl
    ralxfrd
    bitr4d
    @7
    @60
    @47
    vu
    vx
    cB
    @85
    ralrab
    @3
    @56
    @87
    vz
    vx
    cB
    @84
    ralrab
    3bitr4g
    @101
    @39
    @54
    @91
    @49
    @89
    wb
    @92
    @1
    @54
    @91
    simplr
    @55
    @91
    simpr
    cB
    cK
    @14
    c.pe
    @25
    @46
    glbcon.b
    @35
    glbcon.o
    oplecon3b
    syl3anc
    imbi12d
    ralbidva
    bitr4d
    anbi12d
    riotabidva
    @1
    @8
    cB
    wss
    #
    @9
    @53
    wceq
    @7
    vx
    cB
    ssrab2
    @1
    @112
    wa
    @52
    vv
    vu
    vt
    cB
    @8
    cU
    cK
    @14
    chlt
    glbcon.b
    @35
    glbcon.u
    @52
    biid
    @1
    @112
    simpl
    @1
    @112
    simpr
    lubval
    mpan2
    eqtr4d
    fveq2d
    3eqtrd
    sylan9eqr
end
