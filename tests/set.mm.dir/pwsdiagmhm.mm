include "cmnd.mm"
include "wcel.mm"
include "wa.mm"
include "cbs.mm"
include "cfv.mm"
include "wf.mm"
include "cv.mm"
include "cplusg.mm"
include "co.mm"
include "wceq.mm"
include "wral.mm"
include "c0g.mm"
include "w3a.mm"
include "cmhm.mm"
include "simpl.mm"
include "pwsmnd.mm"
include "jca.mm"
include "cmap.mm"
include "cvv.mm"
include "fvex.mm"
include "eqeltri.mm"
include "fdiagfn.mm"
include "mpan.mm"
include "adantl.mm"
include "pwsbas.mm"
include "feq3d.mm"
include "mpbid.mm"
include "csn.mm"
include "cxp.mm"
include "simplr.mm"
include "eqid.mm"
include "mndcl.mm"
include "3expb.mm"
include "adantlr.mm"
include "fvdiagfn.mm"
include "syl2anc.mm"
include "cof.mm"
include "oveqan12d.mm"
include "anandis.mm"
include "adantll.mm"
include "simpll.mm"
include "pwsdiagel.mm"
include "adantrr.mm"
include "adantrl.mm"
include "pwsplusgval.mm"
include "id.mm"
include "vex.mm"
include "a1i.mm"
include "ofc12.mm"
include "ad2antlr.mm"
include "3eqtrd.mm"
include "eqtr4d.mm"
include "ralrimivva.mm"
include "simpr.mm"
include "mndidcl.mm"
include "adantr.mm"
include "pws0g.mm"
include "eqtrd.mm"
include "3jca.mm"
include "ismhm.mm"
include "sylanbrc.mm"

theorem pwsdiagmhm
  let vx: setvar x
  let cB: class B
  let cR: class R
  let cF: class F
  let cI: class I
  let cW: class W
  let cY: class Y
  let va: setvar a
  let vb: setvar b
  assume pwsdiagmhm.y: |- Y = ( R ^s I )
  assume pwsdiagmhm.b: |- B = ( Base ` R )
  assume pwsdiagmhm.f: |- F = ( x e. B |-> ( I X. { x } ) )

  disjoint Y x
  disjoint R x
  disjoint I x
  disjoint B x
  disjoint W x
  disjoint Y a
  disjoint Y b
  disjoint a x
  disjoint b x
  disjoint a b
  disjoint R a
  disjoint R b
  disjoint I a
  disjoint I b
  disjoint B a
  disjoint B b
  disjoint F a
  disjoint F b
  disjoint W a
  disjoint W b
  assert |- ( ( R e. Mnd /\ I e. W ) -> F e. ( R MndHom Y ) )

  proof
    cR
    cmnd
    wcel
    #
    cI
    cW
    wcel
    #
    wa
    #
    @0
    cY
    cmnd
    wcel
    #
    wa
    cB
    cY
    cbs
    cfv
    #
    cF
    wf
    #
    va
    cv
    #
    vb
    cv
    #
    cR
    cplusg
    cfv
    #
    co
    #
    cF
    cfv
    #
    @6
    cF
    cfv
    #
    @7
    cF
    cfv
    #
    cY
    cplusg
    cfv
    #
    co
    #
    wceq
    #
    vb
    cB
    wral
    va
    cB
    wral
    #
    cR
    c0g
    cfv
    #
    cF
    cfv
    #
    cY
    c0g
    cfv
    #
    wceq
    #
    w3a
    cF
    cR
    cY
    cmhm
    co
    wcel
    @2
    @0
    @3
    @0
    @1
    simpl
    cR
    cI
    cW
    cY
    pwsdiagmhm.y
    pwsmnd
    jca
    @2
    @5
    @16
    @20
    @2
    cB
    cB
    cI
    cmap
    co
    #
    cF
    wf
    #
    @5
    @1
    @22
    @0
    cB
    cvv
    wcel
    @1
    @22
    cB
    cR
    cbs
    cfv
    cvv
    pwsdiagmhm.b
    cR
    cbs
    fvex
    eqeltri
    vx
    cB
    cF
    cI
    cvv
    cW
    pwsdiagmhm.f
    fdiagfn
    mpan
    adantl
    @2
    @21
    @4
    cF
    cB
    cB
    cR
    cI
    cmnd
    cW
    cY
    pwsdiagmhm.y
    pwsdiagmhm.b
    pwsbas
    feq3d
    mpbid
    @2
    @15
    va
    vb
    cB
    cB
    @2
    @6
    cB
    wcel
    #
    @7
    cB
    wcel
    #
    wa
    #
    wa
    #
    @10
    cI
    @9
    csn
    cxp
    #
    @14
    @26
    @1
    @9
    cB
    wcel
    #
    @10
    @27
    wceq
    @0
    @1
    @25
    simplr
    #
    @0
    @25
    @28
    @1
    @0
    @23
    @24
    @28
    cB
    @8
    cR
    @6
    @7
    pwsdiagmhm.b
    @8
    eqid
    #
    mndcl
    3expb
    adantlr
    vx
    cB
    cF
    cI
    cW
    @9
    pwsdiagmhm.f
    fvdiagfn
    syl2anc
    @26
    @14
    cI
    @6
    csn
    cxp
    #
    cI
    @7
    csn
    cxp
    #
    @13
    co
    #
    @31
    @32
    @8
    cof
    co
    #
    @27
    @1
    @25
    @14
    @33
    wceq
    #
    @0
    @1
    @23
    @24
    @35
    @1
    @23
    wa
    @1
    @24
    wa
    @11
    @31
    @12
    @32
    @13
    vx
    cB
    cF
    cI
    cW
    @6
    pwsdiagmhm.f
    fvdiagfn
    vx
    cB
    cF
    cI
    cW
    @7
    pwsdiagmhm.f
    fvdiagfn
    oveqan12d
    anandis
    adantll
    @26
    @4
    @8
    @13
    cR
    @31
    @32
    cI
    cmnd
    cW
    cY
    pwsdiagmhm.y
    @4
    eqid
    #
    @0
    @1
    @25
    simpll
    @29
    @2
    @23
    @31
    @4
    wcel
    @24
    @6
    cB
    @4
    cR
    cI
    cmnd
    cW
    cY
    pwsdiagmhm.y
    pwsdiagmhm.b
    @36
    pwsdiagel
    adantrr
    @2
    @24
    @32
    @4
    wcel
    @23
    @7
    cB
    @4
    cR
    cI
    cmnd
    cW
    cY
    pwsdiagmhm.y
    pwsdiagmhm.b
    @36
    pwsdiagel
    adantrl
    @30
    @13
    eqid
    #
    pwsplusgval
    @1
    @34
    @27
    wceq
    @0
    @25
    @1
    cI
    @6
    @7
    @8
    cW
    cvv
    cvv
    @1
    id
    @6
    cvv
    wcel
    @1
    va
    vex
    a1i
    @7
    cvv
    wcel
    @1
    vb
    vex
    a1i
    ofc12
    ad2antlr
    3eqtrd
    eqtr4d
    ralrimivva
    @2
    @18
    cI
    @17
    csn
    cxp
    #
    @19
    @2
    @1
    @17
    cB
    wcel
    #
    @18
    @38
    wceq
    @0
    @1
    simpr
    @0
    @39
    @1
    cB
    cR
    @17
    pwsdiagmhm.b
    @17
    eqid
    #
    mndidcl
    adantr
    vx
    cB
    cF
    cI
    cW
    @17
    pwsdiagmhm.f
    fvdiagfn
    syl2anc
    cR
    cI
    cW
    cY
    @17
    pwsdiagmhm.y
    @40
    pws0g
    eqtrd
    3jca
    va
    vb
    cB
    @4
    @8
    @13
    cR
    cY
    cF
    @19
    @17
    pwsdiagmhm.b
    @36
    @30
    @37
    @40
    @19
    eqid
    ismhm
    sylanbrc
end
