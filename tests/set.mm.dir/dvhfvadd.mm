include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "cplusg.mm"
include "cfv.mm"
include "cxp.mm"
include "cv.mm"
include "c1st.mm"
include "ccom.mm"
include "c2nd.mm"
include "co.mm"
include "cop.mm"
include "cmpt2.mm"
include "cnx.mm"
include "cbs.mm"
include "cmpt.mm"
include "csca.mm"
include "cedring.mm"
include "ctp.mm"
include "cvsca.mm"
include "csn.mm"
include "cun.mm"
include "eqid.mm"
include "dvhset.mm"
include "fveq2d.mm"
include "w3a.mm"
include "wceq.mm"
include "dvhsca.mm"
include "syl5eq.mm"
include "oveqd.mm"
include "3ad2ant1.mm"
include "xp2nd.mm"
include "anim12i.mm"
include "erngplus.mm"
include "sylan2.mm"
include "3impb.mm"
include "eqtrd.mm"
include "opeq2d.mm"
include "mpt2eq3dva.mm"
include "cvv.mm"
include "cltrn.mm"
include "fvex.mm"
include "eqeltri.mm"
include "ctendo.mm"
include "xpex.mm"
include "mpt2ex.mm"
include "lmodplusg.mm"
include "ax-mp.mm"
include "syl6req.mm"
include "3eqtr4g.mm"

theorem dvhfvadd
  let cD: class D
  let c.pl: class .+
  let c.pd: class .+^
  let c.pb: class .+b
  let cT: class T
  let cU: class U
  let vf: setvar f
  let vg: setvar g
  let cE: class E
  let cH: class H
  let cK: class K
  let cW: class W
  let vh: setvar h
  let vs: setvar s
  assume dvhfvadd.h: |- H = ( LHyp ` K )
  assume dvhfvadd.t: |- T = ( ( LTrn ` K ) ` W )
  assume dvhfvadd.e: |- E = ( ( TEndo ` K ) ` W )
  assume dvhfvadd.u: |- U = ( ( DVecH ` K ) ` W )
  assume dvhfvadd.f: |- D = ( Scalar ` U )
  assume dvhfvadd.p: |- .+^ = ( +g ` D )
  assume dvhfvadd.a: |- .+b = ( f e. ( T X. E ) , g e. ( T X. E ) |-> <. ( ( 1st ` f ) o. ( 1st ` g ) ) , ( ( 2nd ` f ) .+^ ( 2nd ` g ) ) >. )
  assume dvhfvadd.s: |- .+ = ( +g ` U )

  disjoint f g
  disjoint E f
  disjoint E g
  disjoint H f
  disjoint H g
  disjoint K f
  disjoint K g
  disjoint T f
  disjoint T g
  disjoint W f
  disjoint W g
  disjoint f h
  disjoint f s
  disjoint g h
  disjoint g s
  disjoint h s
  disjoint K h
  disjoint K s
  disjoint T h
  disjoint W h
  disjoint W s
  assert |- ( ( K e. HL /\ W e. H ) -> .+ = .+b )

  proof
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    #
    cU
    cplusg
    cfv
    #
    vf
    vg
    cT
    cE
    cxp
    #
    @2
    vf
    cv
    #
    c1st
    cfv
    #
    vg
    cv
    #
    c1st
    cfv
    ccom
    #
    @3
    c2nd
    cfv
    #
    @5
    c2nd
    cfv
    #
    c.pd
    co
    #
    cop
    #
    cmpt2
    #
    c.pl
    c.pb
    @0
    @1
    cnx
    cbs
    cfv
    @2
    cop
    cnx
    cplusg
    cfv
    vf
    vg
    @2
    @2
    @6
    vh
    cT
    vh
    cv
    #
    @7
    cfv
    @12
    @8
    cfv
    ccom
    cmpt
    #
    cop
    #
    cmpt2
    #
    cop
    cnx
    csca
    cfv
    cW
    cK
    cedring
    cfv
    cfv
    #
    cop
    ctp
    cnx
    cvsca
    cfv
    vs
    vf
    cE
    @2
    @4
    vs
    cv
    #
    cfv
    @17
    @7
    ccom
    cop
    cmpt2
    #
    cop
    csn
    cun
    #
    cplusg
    cfv
    #
    @11
    @0
    cU
    @19
    cplusg
    @16
    cT
    cU
    vf
    vg
    vh
    cE
    cH
    cK
    cW
    chlt
    vs
    dvhfvadd.h
    dvhfvadd.t
    dvhfvadd.e
    @16
    eqid
    #
    dvhfvadd.u
    dvhset
    fveq2d
    @0
    @11
    @15
    @20
    @0
    vf
    vg
    @2
    @2
    @10
    @14
    @0
    @3
    @2
    wcel
    #
    @5
    @2
    wcel
    #
    w3a
    #
    @9
    @13
    @6
    @24
    @9
    @7
    @8
    @16
    cplusg
    cfv
    #
    co
    #
    @13
    @0
    @22
    @9
    @26
    wceq
    @23
    @0
    c.pd
    @25
    @7
    @8
    @0
    c.pd
    cD
    cplusg
    cfv
    @25
    dvhfvadd.p
    @0
    cD
    @16
    cplusg
    @16
    cU
    cD
    cH
    cK
    cW
    chlt
    dvhfvadd.h
    @21
    dvhfvadd.u
    dvhfvadd.f
    dvhsca
    fveq2d
    syl5eq
    oveqd
    3ad2ant1
    @0
    @22
    @23
    @26
    @13
    wceq
    #
    @22
    @23
    wa
    @0
    @7
    cE
    wcel
    #
    @8
    cE
    wcel
    #
    wa
    @27
    @22
    @28
    @23
    @29
    @3
    cT
    cE
    xp2nd
    @5
    cT
    cE
    xp2nd
    anim12i
    @16
    @25
    cT
    @7
    vh
    cE
    cH
    cK
    @8
    cW
    dvhfvadd.h
    dvhfvadd.t
    dvhfvadd.e
    @21
    @25
    eqid
    erngplus
    sylan2
    3impb
    eqtrd
    opeq2d
    mpt2eq3dva
    @15
    cvv
    wcel
    @15
    @20
    wceq
    vf
    vg
    @2
    @2
    @14
    cT
    cE
    cT
    cW
    cK
    cltrn
    cfv
    #
    cfv
    cvv
    dvhfvadd.t
    cW
    @30
    fvex
    eqeltri
    cE
    cW
    cK
    ctendo
    cfv
    #
    cfv
    cvv
    dvhfvadd.e
    cW
    @31
    fvex
    eqeltri
    xpex
    #
    @32
    mpt2ex
    @2
    @15
    @18
    @16
    @19
    cvv
    @19
    eqid
    lmodplusg
    ax-mp
    syl6req
    eqtrd
    dvhfvadd.s
    dvhfvadd.a
    3eqtr4g
end
