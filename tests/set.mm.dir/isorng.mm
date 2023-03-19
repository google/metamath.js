include "crg.mm"
include "cogrp.mm"
include "cin.mm"
include "wcel.mm"
include "cv.mm"
include "wbr.mm"
include "wa.mm"
include "co.mm"
include "wi.mm"
include "wral.mm"
include "corng.mm"
include "w3a.mm"
include "elin.mm"
include "anbi1i.mm"
include "cple.mm"
include "cfv.mm"
include "wsbc.mm"
include "cmulr.mm"
include "c0g.mm"
include "cbs.mm"
include "wceq.mm"
include "cvv.mm"
include "fvexd.mm"
include "simpr.mm"
include "simpl.mm"
include "fveq2d.mm"
include "syl6eqr.mm"
include "eqtrd.mm"
include "oveqd.mm"
include "breq2d.mm"
include "imbi2d.mm"
include "2ralbidv.mm"
include "sbcbidv.mm"
include "sbcied.mm"
include "wb.mm"
include "fveq2.mm"
include "adantr.mm"
include "raleq.mm"
include "raleqbi1dv.mm"
include "syl.mm"
include "breq1d.mm"
include "anbi12d.mm"
include "imbi12d.mm"
include "bitr2d.mm"
include "breqd.mm"
include "3bitr3d.mm"
include "df-orng.mm"
include "elrab2.mm"
include "df-3an.mm"
include "3bitr4i.mm"

theorem isorng
  let cB: class B
  let cR: class R
  let c.x: class .x.
  let c.le: class .<_
  let c.0: class .0.
  let va: setvar a
  let vb: setvar b
  let vl: setvar l
  let vr: setvar r
  let vt: setvar t
  let vv: setvar v
  let vz: setvar z
  assume isorng.0: |- B = ( Base ` R )
  assume isorng.1: |- .0. = ( 0g ` R )
  assume isorng.2: |- .x. = ( .r ` R )
  assume isorng.3: |- .<_ = ( le ` R )

  disjoint a b
  disjoint B a
  disjoint B b
  disjoint R a
  disjoint R b
  disjoint a l
  disjoint a r
  disjoint a t
  disjoint a v
  disjoint a z
  disjoint b l
  disjoint b r
  disjoint b t
  disjoint b v
  disjoint b z
  disjoint l r
  disjoint l t
  disjoint l v
  disjoint l z
  disjoint B l
  disjoint r t
  disjoint r v
  disjoint r z
  disjoint B r
  disjoint t v
  disjoint t z
  disjoint B t
  disjoint v z
  disjoint B v
  disjoint B z
  disjoint R l
  disjoint R r
  disjoint R t
  disjoint R v
  disjoint R z
  disjoint .0. l
  disjoint .0. r
  disjoint .0. t
  disjoint .0. z
  disjoint .<_ l
  disjoint .<_ r
  disjoint .x. l
  disjoint .x. r
  disjoint .x. t
  assert |- ( R e. oRing <-> ( R e. Ring /\ R e. oGrp /\ A. a e. B A. b e. B ( ( .0. .<_ a /\ .0. .<_ b ) -> .0. .<_ ( a .x. b ) ) ) )

  proof
    cR
    crg
    cogrp
    cin
    #
    wcel
    #
    c.0
    va
    cv
    #
    c.le
    wbr
    #
    c.0
    vb
    cv
    #
    c.le
    wbr
    #
    wa
    #
    c.0
    @2
    @4
    c.x
    co
    #
    c.le
    wbr
    #
    wi
    #
    vb
    cB
    wral
    va
    cB
    wral
    #
    wa
    cR
    crg
    wcel
    #
    cR
    cogrp
    wcel
    #
    wa
    #
    @10
    wa
    cR
    corng
    wcel
    @11
    @12
    @10
    w3a
    @1
    @13
    @10
    cR
    crg
    cogrp
    elin
    anbi1i
    vz
    cv
    #
    @2
    vl
    cv
    #
    wbr
    #
    @14
    @4
    @15
    wbr
    #
    wa
    #
    @14
    @2
    @4
    vt
    cv
    #
    co
    #
    @15
    wbr
    #
    wi
    #
    vb
    vv
    cv
    #
    wral
    #
    va
    @23
    wral
    #
    vl
    vr
    cv
    #
    cple
    cfv
    #
    wsbc
    #
    vt
    @26
    cmulr
    cfv
    #
    wsbc
    #
    vz
    @26
    c0g
    cfv
    #
    wsbc
    #
    vv
    @26
    cbs
    cfv
    #
    wsbc
    #
    @10
    vr
    cR
    @0
    corng
    @26
    cR
    wceq
    #
    c.0
    @2
    @15
    wbr
    #
    c.0
    @4
    @15
    wbr
    #
    wa
    #
    c.0
    @20
    @15
    wbr
    #
    wi
    #
    vb
    cB
    wral
    va
    cB
    wral
    #
    vl
    @27
    wsbc
    #
    vt
    @29
    wsbc
    #
    @38
    c.0
    @7
    @15
    wbr
    #
    wi
    #
    vb
    cB
    wral
    va
    cB
    wral
    #
    vl
    @27
    wsbc
    #
    @34
    @10
    @35
    @42
    @47
    vt
    @29
    cvv
    @35
    @26
    cmulr
    fvexd
    @35
    @19
    @29
    wceq
    #
    wa
    #
    @41
    @46
    vl
    @27
    @49
    @40
    @45
    va
    vb
    cB
    cB
    @49
    @39
    @44
    @38
    @49
    @20
    @7
    c.0
    @15
    @49
    @19
    c.x
    @2
    @4
    @49
    @19
    @29
    c.x
    @35
    @48
    simpr
    @49
    @29
    cR
    cmulr
    cfv
    c.x
    @49
    @26
    cR
    cmulr
    @35
    @48
    simpl
    fveq2d
    isorng.2
    syl6eqr
    eqtrd
    oveqd
    breq2d
    imbi2d
    2ralbidv
    sbcbidv
    sbcied
    @35
    @34
    @22
    vb
    cB
    wral
    #
    va
    cB
    wral
    #
    vl
    @27
    wsbc
    #
    vt
    @29
    wsbc
    #
    vz
    @31
    wsbc
    #
    @43
    @35
    @32
    @54
    vv
    @33
    cvv
    @35
    @26
    cbs
    fvexd
    @35
    @23
    @33
    wceq
    #
    wa
    #
    @30
    @53
    vz
    @31
    @56
    @28
    @52
    vt
    @29
    @56
    @25
    @51
    vl
    @27
    @56
    @23
    cB
    wceq
    @25
    @51
    wb
    @56
    @23
    @33
    cB
    @35
    @55
    simpr
    @35
    @33
    cB
    wceq
    @55
    @35
    @33
    cR
    cbs
    cfv
    cB
    @26
    cR
    cbs
    fveq2
    isorng.0
    syl6eqr
    adantr
    eqtrd
    @24
    @50
    va
    @23
    cB
    @22
    vb
    @23
    cB
    raleq
    raleqbi1dv
    syl
    sbcbidv
    sbcbidv
    sbcbidv
    sbcied
    @35
    @53
    @43
    vz
    @31
    cvv
    @35
    @26
    c0g
    fvexd
    @35
    @14
    @31
    wceq
    #
    wa
    #
    @52
    @42
    vt
    @29
    @58
    @51
    @41
    vl
    @27
    @58
    @22
    @40
    va
    vb
    cB
    cB
    @58
    @18
    @38
    @21
    @39
    @58
    @16
    @36
    @17
    @37
    @58
    @14
    c.0
    @2
    @15
    @58
    @14
    @31
    c.0
    @35
    @57
    simpr
    @35
    @31
    c.0
    wceq
    @57
    @35
    @31
    cR
    c0g
    cfv
    c.0
    @26
    cR
    c0g
    fveq2
    isorng.1
    syl6eqr
    adantr
    eqtrd
    #
    breq1d
    @58
    @14
    c.0
    @4
    @15
    @59
    breq1d
    anbi12d
    @58
    @14
    c.0
    @20
    @15
    @59
    breq1d
    imbi12d
    2ralbidv
    sbcbidv
    sbcbidv
    sbcied
    bitr2d
    @35
    @46
    @10
    vl
    @27
    cvv
    @35
    @26
    cple
    fvexd
    @35
    @15
    @27
    wceq
    #
    wa
    #
    @45
    @9
    va
    vb
    cB
    cB
    @61
    @38
    @6
    @44
    @8
    @61
    @36
    @3
    @37
    @5
    @61
    @15
    c.le
    c.0
    @2
    @61
    @15
    @27
    c.le
    @35
    @60
    simpr
    @61
    @27
    cR
    cple
    cfv
    c.le
    @61
    @26
    cR
    cple
    @35
    @60
    simpl
    fveq2d
    isorng.3
    syl6eqr
    eqtrd
    #
    breqd
    @61
    @15
    c.le
    c.0
    @4
    @62
    breqd
    anbi12d
    @61
    @15
    c.le
    c.0
    @7
    @62
    breqd
    imbi12d
    2ralbidv
    sbcied
    3bitr3d
    vz
    vv
    vt
    vr
    va
    vb
    vl
    df-orng
    elrab2
    @11
    @12
    @10
    df-3an
    3bitr4i
end
