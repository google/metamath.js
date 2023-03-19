include "clmod.mm"
include "wcel.mm"
include "wne.mm"
include "wa.mm"
include "w3a.mm"
include "cpr.mm"
include "clinc.mm"
include "cfv.mm"
include "co.mm"
include "cv.mm"
include "cvsca.mm"
include "cmpt.mm"
include "cgsu.mm"
include "csca.mm"
include "cbs.mm"
include "cmap.mm"
include "cpw.mm"
include "wceq.mm"
include "simpl.mm"
include "3ad2ant1.mm"
include "cvv.mm"
include "fveq2i.mm"
include "eqtri.mm"
include "eleq2i.mm"
include "biimpi.mm"
include "anim2i.mm"
include "3ad2ant2.mm"
include "3ad2ant3.mm"
include "fvexd.mm"
include "ancoms.mm"
include "mapprop.mm"
include "syl3anc.mm"
include "adantr.mm"
include "prelpwi.mm"
include "syl2an.mm"
include "3adant1.mm"
include "lincval.mm"
include "ccmn.mm"
include "lmodcmn.mm"
include "simpr.mm"
include "3anim123i.mm"
include "3anrot.mm"
include "sylib.mm"
include "cop.mm"
include "a1i.mm"
include "fveq1d.mm"
include "simprl.mm"
include "simprr.mm"
include "fvpr1g.mm"
include "eqtrd.mm"
include "oveq1d.mm"
include "eqid.mm"
include "lmodvscl.mm"
include "eqeltrd.mm"
include "3adant3.mm"
include "fvpr2g.mm"
include "3adant2.mm"
include "fveq2.mm"
include "id.mm"
include "oveq12d.mm"
include "gsumpr.mm"
include "syl112anc.mm"
include "eqcomd.mm"
include "fveq1i.mm"
include "syl5eq.mm"
include "eqidd.mm"
include "oveq123d.mm"
include "3eqtrd.mm"

theorem lincvalpr
  let cB: class B
  let c.pl: class .+
  let cR: class R
  let cS: class S
  let c.x: class .x.
  let cF: class F
  let cM: class M
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  let vv: setvar v
  let vk: setvar k
  let vx: setvar x
  assume lincvalsn.b: |- B = ( Base ` M )
  assume lincvalsn.s: |- S = ( Scalar ` M )
  assume lincvalsn.r: |- R = ( Base ` S )
  assume lincvalsn.t: |- .x. = ( .s ` M )
  assume lincvalpr.p: |- .+ = ( +g ` M )
  assume lincvalpr.f: |- F = { <. V , X >. , <. W , Y >. }


  assert |- ( ( ( M e. LMod /\ V =/= W ) /\ ( V e. B /\ X e. R ) /\ ( W e. B /\ Y e. R ) ) -> ( F ( linC ` M ) { V , W } ) = ( ( X .x. V ) .+ ( Y .x. W ) ) )

  proof
    cM
    clmod
    wcel
    #
    cV
    cW
    wne
    #
    wa
    #
    cV
    cB
    wcel
    #
    cX
    cR
    wcel
    #
    wa
    #
    cW
    cB
    wcel
    #
    cY
    cR
    wcel
    #
    wa
    #
    w3a
    #
    cF
    cV
    cW
    cpr
    #
    cM
    clinc
    cfv
    co
    #
    cM
    vv
    @10
    vv
    cv
    #
    cF
    cfv
    #
    @12
    cM
    cvsca
    cfv
    #
    co
    #
    cmpt
    cgsu
    co
    #
    cV
    cF
    cfv
    #
    cV
    @14
    co
    #
    cW
    cF
    cfv
    #
    cW
    @14
    co
    #
    c.pl
    co
    #
    cX
    cV
    c.x
    co
    #
    cY
    cW
    c.x
    co
    #
    c.pl
    co
    @9
    @0
    cF
    cM
    csca
    cfv
    #
    cbs
    cfv
    #
    @10
    cmap
    co
    wcel
    #
    @10
    cM
    cbs
    cfv
    #
    cpw
    wcel
    #
    @11
    @16
    wceq
    @2
    @5
    @0
    @8
    @0
    @1
    simpl
    #
    3ad2ant1
    @9
    @3
    cX
    @25
    wcel
    #
    wa
    #
    @6
    cY
    @25
    wcel
    #
    wa
    #
    @1
    @25
    cvv
    wcel
    #
    wa
    #
    @26
    @5
    @2
    @31
    @8
    @4
    @30
    @3
    @4
    @30
    cR
    @25
    cX
    cR
    cS
    cbs
    cfv
    @25
    lincvalsn.r
    cS
    @24
    cbs
    lincvalsn.s
    fveq2i
    eqtri
    #
    eleq2i
    biimpi
    anim2i
    3ad2ant2
    @8
    @2
    @33
    @5
    @7
    @32
    @6
    @7
    @32
    cR
    @25
    cY
    @36
    eleq2i
    biimpi
    anim2i
    3ad2ant3
    @2
    @5
    @35
    @8
    @1
    @0
    @35
    @0
    @34
    @1
    @0
    @24
    cbs
    fvexd
    anim2i
    ancoms
    3ad2ant1
    cX
    cY
    @25
    cF
    cB
    cvv
    cV
    cW
    lincvalpr.f
    mapprop
    syl3anc
    @5
    @8
    @28
    @2
    @5
    cV
    @27
    wcel
    #
    cW
    @27
    wcel
    #
    @28
    @8
    @3
    @37
    @4
    @3
    @37
    cB
    @27
    cV
    lincvalsn.b
    eleq2i
    biimpi
    adantr
    @6
    @38
    @7
    @6
    @38
    cB
    @27
    cW
    lincvalsn.b
    eleq2i
    biimpi
    adantr
    cV
    cW
    @27
    prelpwi
    syl2an
    3adant1
    vv
    cF
    cM
    @10
    clmod
    lincval
    syl3anc
    @9
    cM
    ccmn
    wcel
    #
    @3
    @6
    @1
    w3a
    #
    @18
    cB
    wcel
    #
    @20
    cB
    wcel
    #
    @16
    @21
    wceq
    @2
    @5
    @39
    @8
    @0
    @39
    @1
    cM
    lmodcmn
    adantr
    3ad2ant1
    @9
    @1
    @3
    @6
    w3a
    @40
    @2
    @1
    @5
    @3
    @8
    @6
    @0
    @1
    simpr
    #
    @3
    @4
    simpl
    #
    @6
    @7
    simpl
    #
    3anim123i
    @1
    @3
    @6
    3anrot
    sylib
    @2
    @5
    @41
    @8
    @2
    @5
    wa
    #
    @18
    cX
    cV
    @14
    co
    #
    cB
    @46
    @17
    cX
    cV
    @14
    @46
    @17
    cV
    cV
    cX
    cop
    cW
    cY
    cop
    cpr
    #
    cfv
    #
    cX
    @46
    cV
    cF
    @48
    cF
    @48
    wceq
    #
    @46
    lincvalpr.f
    a1i
    fveq1d
    @46
    @3
    @4
    @1
    @49
    cX
    wceq
    #
    @2
    @3
    @4
    simprl
    #
    @2
    @3
    @4
    simprr
    #
    @2
    @1
    @5
    @43
    adantr
    cV
    cW
    cX
    cY
    cB
    cR
    fvpr1g
    #
    syl3anc
    eqtrd
    oveq1d
    @46
    @0
    @4
    @3
    @47
    cB
    wcel
    @2
    @0
    @5
    @29
    adantr
    @53
    @52
    cX
    @14
    cS
    cR
    cB
    cM
    cV
    lincvalsn.b
    lincvalsn.s
    @14
    eqid
    #
    lincvalsn.r
    lmodvscl
    syl3anc
    eqeltrd
    3adant3
    @2
    @8
    @42
    @5
    @2
    @8
    wa
    #
    @20
    cY
    cW
    @14
    co
    #
    cB
    @56
    @19
    cY
    cW
    @14
    @56
    @19
    cW
    @48
    cfv
    #
    cY
    @56
    cW
    cF
    @48
    @50
    @56
    lincvalpr.f
    a1i
    fveq1d
    @56
    @6
    @7
    @1
    @58
    cY
    wceq
    #
    @2
    @6
    @7
    simprl
    #
    @2
    @6
    @7
    simprr
    #
    @2
    @1
    @8
    @43
    adantr
    cV
    cW
    cX
    cY
    cB
    cR
    fvpr2g
    #
    syl3anc
    eqtrd
    oveq1d
    @56
    @0
    @7
    @6
    @57
    cB
    wcel
    @2
    @0
    @8
    @29
    adantr
    @61
    @60
    cY
    @14
    cS
    cR
    cB
    cM
    cW
    lincvalsn.b
    lincvalsn.s
    @55
    lincvalsn.r
    lmodvscl
    syl3anc
    eqeltrd
    3adant2
    @15
    cB
    @18
    @20
    c.pl
    vv
    cM
    cV
    cW
    cB
    cB
    lincvalsn.b
    lincvalpr.p
    @12
    cV
    wceq
    #
    @13
    @17
    @12
    cV
    @14
    @12
    cV
    cF
    fveq2
    @63
    id
    oveq12d
    @12
    cW
    wceq
    #
    @13
    @19
    @12
    cW
    @14
    @12
    cW
    cF
    fveq2
    @64
    id
    oveq12d
    gsumpr
    syl112anc
    @9
    @18
    @22
    @20
    @23
    c.pl
    @9
    @17
    cX
    cV
    cV
    @14
    c.x
    @9
    c.x
    @14
    c.x
    @14
    wceq
    @9
    lincvalsn.t
    a1i
    eqcomd
    #
    @9
    @17
    @49
    cX
    cV
    cF
    @48
    lincvalpr.f
    fveq1i
    @9
    @3
    @4
    @1
    @51
    @5
    @2
    @3
    @8
    @44
    3ad2ant2
    @5
    @2
    @4
    @8
    @3
    @4
    simpr
    3ad2ant2
    @2
    @5
    @1
    @8
    @43
    3ad2ant1
    #
    @54
    syl3anc
    syl5eq
    @9
    cV
    eqidd
    oveq123d
    @9
    @19
    cY
    cW
    cW
    @14
    c.x
    @65
    @9
    @19
    @58
    cY
    cW
    cF
    @48
    lincvalpr.f
    fveq1i
    @9
    @6
    @7
    @1
    @59
    @8
    @2
    @6
    @5
    @45
    3ad2ant3
    @8
    @2
    @7
    @5
    @6
    @7
    simpr
    3ad2ant3
    @66
    @62
    syl3anc
    syl5eq
    @9
    cW
    eqidd
    oveq123d
    oveq12d
    3eqtrd
end
