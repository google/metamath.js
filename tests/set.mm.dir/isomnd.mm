include "comnd.mm"
include "wcel.mm"
include "cmnd.mm"
include "ctos.mm"
include "cv.mm"
include "wbr.mm"
include "co.mm"
include "wi.mm"
include "wral.mm"
include "wa.mm"
include "w3a.mm"
include "cple.mm"
include "cfv.mm"
include "wsbc.mm"
include "cplusg.mm"
include "cbs.mm"
include "wceq.mm"
include "cvv.mm"
include "fvexd.mm"
include "wb.mm"
include "simpr.mm"
include "fveq2.mm"
include "adantr.mm"
include "eqtrd.mm"
include "syl6eqr.mm"
include "raleq.mm"
include "raleqbi1dv.mm"
include "syl.mm"
include "anbi2d.mm"
include "sbcbidv.mm"
include "sbcied.mm"
include "oveqd.mm"
include "breq12d.mm"
include "imbi2d.mm"
include "ralbidv.mm"
include "2ralbidv.mm"
include "simpl.mm"
include "fveq2d.mm"
include "breqd.mm"
include "imbi12d.mm"
include "eleq1.mm"
include "anbi1d.mm"
include "bitrd.mm"
include "3bitrd.mm"
include "df-omnd.mm"
include "elrab2.mm"
include "3anass.mm"
include "bitr4i.mm"

theorem isomnd
  let cB: class B
  let c.pl: class .+
  let c.le: class .<_
  let cM: class M
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vl: setvar l
  let vm: setvar m
  let vp: setvar p
  let vv: setvar v
  assume isomnd.0: |- B = ( Base ` M )
  assume isomnd.1: |- .+ = ( +g ` M )
  assume isomnd.2: |- .<_ = ( le ` M )

  disjoint a b
  disjoint a c
  disjoint B a
  disjoint b c
  disjoint B b
  disjoint B c
  disjoint M a
  disjoint M b
  disjoint M c
  disjoint a l
  disjoint a m
  disjoint a p
  disjoint a v
  disjoint b l
  disjoint b m
  disjoint b p
  disjoint b v
  disjoint c l
  disjoint c m
  disjoint c p
  disjoint c v
  disjoint l m
  disjoint l p
  disjoint l v
  disjoint B l
  disjoint m p
  disjoint m v
  disjoint B m
  disjoint p v
  disjoint B p
  disjoint B v
  disjoint M l
  disjoint M m
  disjoint M p
  disjoint M v
  disjoint .+ l
  disjoint .+ m
  disjoint .+ p
  disjoint .<_ l
  disjoint .<_ m
  assert |- ( M e. oMnd <-> ( M e. Mnd /\ M e. Toset /\ A. a e. B A. b e. B A. c e. B ( a .<_ b -> ( a .+ c ) .<_ ( b .+ c ) ) ) )

  proof
    cM
    comnd
    wcel
    cM
    cmnd
    wcel
    #
    cM
    ctos
    wcel
    #
    va
    cv
    #
    vb
    cv
    #
    c.le
    wbr
    #
    @2
    vc
    cv
    #
    c.pl
    co
    #
    @3
    @5
    c.pl
    co
    #
    c.le
    wbr
    #
    wi
    #
    vc
    cB
    wral
    #
    vb
    cB
    wral
    va
    cB
    wral
    #
    wa
    #
    wa
    @0
    @1
    @11
    w3a
    vm
    cv
    #
    ctos
    wcel
    #
    @2
    @3
    vl
    cv
    #
    wbr
    #
    @2
    @5
    vp
    cv
    #
    co
    #
    @3
    @5
    @17
    co
    #
    @15
    wbr
    #
    wi
    #
    vc
    vv
    cv
    #
    wral
    #
    vb
    @22
    wral
    #
    va
    @22
    wral
    #
    wa
    #
    vl
    @13
    cple
    cfv
    #
    wsbc
    #
    vp
    @13
    cplusg
    cfv
    #
    wsbc
    #
    vv
    @13
    cbs
    cfv
    #
    wsbc
    #
    @12
    vm
    cM
    cmnd
    comnd
    @13
    cM
    wceq
    #
    @32
    @14
    @21
    vc
    cB
    wral
    #
    vb
    cB
    wral
    #
    va
    cB
    wral
    #
    wa
    #
    vl
    @27
    wsbc
    #
    vp
    @29
    wsbc
    #
    @14
    @16
    @6
    @7
    @15
    wbr
    #
    wi
    #
    vc
    cB
    wral
    #
    vb
    cB
    wral
    va
    cB
    wral
    #
    wa
    #
    vl
    @27
    wsbc
    #
    @12
    @33
    @30
    @39
    vv
    @31
    cvv
    @33
    @13
    cbs
    fvexd
    @33
    @22
    @31
    wceq
    #
    wa
    #
    @28
    @38
    vp
    @29
    @47
    @26
    @37
    vl
    @27
    @47
    @25
    @36
    @14
    @47
    @22
    cB
    wceq
    @25
    @36
    wb
    @47
    @22
    cM
    cbs
    cfv
    #
    cB
    @47
    @22
    @31
    @48
    @33
    @46
    simpr
    @33
    @31
    @48
    wceq
    @46
    @13
    cM
    cbs
    fveq2
    adantr
    eqtrd
    isomnd.0
    syl6eqr
    @24
    @35
    va
    @22
    cB
    @23
    @34
    vb
    @22
    cB
    @21
    vc
    @22
    cB
    raleq
    raleqbi1dv
    raleqbi1dv
    syl
    anbi2d
    sbcbidv
    sbcbidv
    sbcied
    @33
    @38
    @45
    vp
    @29
    cvv
    @33
    @13
    cplusg
    fvexd
    @33
    @17
    @29
    wceq
    #
    wa
    #
    @37
    @44
    vl
    @27
    @50
    @36
    @43
    @14
    @50
    @34
    @42
    va
    vb
    cB
    cB
    @50
    @21
    @41
    vc
    cB
    @50
    @20
    @40
    @16
    @50
    @18
    @6
    @19
    @7
    @15
    @50
    @17
    c.pl
    @2
    @5
    @50
    @17
    cM
    cplusg
    cfv
    #
    c.pl
    @50
    @17
    @29
    @51
    @33
    @49
    simpr
    @33
    @29
    @51
    wceq
    @49
    @13
    cM
    cplusg
    fveq2
    adantr
    eqtrd
    isomnd.1
    syl6eqr
    #
    oveqd
    @50
    @17
    c.pl
    @3
    @5
    @52
    oveqd
    breq12d
    imbi2d
    ralbidv
    2ralbidv
    anbi2d
    sbcbidv
    sbcied
    @33
    @45
    @14
    @11
    wa
    #
    @12
    @33
    @44
    @53
    vl
    @27
    cvv
    @33
    @13
    cple
    fvexd
    @33
    @15
    @27
    wceq
    #
    wa
    #
    @43
    @11
    @14
    @55
    @42
    @10
    va
    vb
    cB
    cB
    @55
    @41
    @9
    vc
    cB
    @55
    @16
    @4
    @40
    @8
    @55
    @15
    c.le
    @2
    @3
    @55
    @15
    cM
    cple
    cfv
    #
    c.le
    @55
    @15
    @27
    @56
    @33
    @54
    simpr
    @55
    @13
    cM
    cple
    @33
    @54
    simpl
    fveq2d
    eqtrd
    isomnd.2
    syl6eqr
    #
    breqd
    @55
    @15
    c.le
    @6
    @7
    @57
    breqd
    imbi12d
    ralbidv
    2ralbidv
    anbi2d
    sbcied
    @33
    @14
    @1
    @11
    @13
    cM
    ctos
    eleq1
    anbi1d
    bitrd
    3bitrd
    vv
    vm
    vp
    va
    vb
    vc
    vl
    df-omnd
    elrab2
    @0
    @1
    @11
    3anass
    bitr4i
end
