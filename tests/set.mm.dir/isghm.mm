include "cghm.mm"
include "co.mm"
include "wcel.mm"
include "cgrp.mm"
include "wa.mm"
include "wf.mm"
include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "wral.mm"
include "cbs.mm"
include "cplusg.mm"
include "wsbc.mm"
include "cab.mm"
include "df-ghm.mm"
include "elmpt2cl.mm"
include "fvex.mm"
include "feq2.mm"
include "raleq.mm"
include "raleqbi1dv.mm"
include "anbi12d.mm"
include "sbcie.mm"
include "fveq2.mm"
include "syl6eqr.mm"
include "feq2d.mm"
include "oveqd.mm"
include "fveq2d.mm"
include "eqeq1d.mm"
include "raleqbidv.mm"
include "syl5bb.mm"
include "abbidv.mm"
include "feq3d.mm"
include "eqeq2d.mm"
include "2ralbidv.mm"
include "cvv.mm"
include "eqeltri.mm"
include "mapex.mm"
include "mp2an.mm"
include "simpl.mm"
include "ss2abi.mm"
include "ssexi.mm"
include "ovmpt2.mm"
include "eleq2d.mm"
include "fex.mm"
include "mpan2.mm"
include "adantr.mm"
include "feq1.mm"
include "fveq1.mm"
include "oveq12d.mm"
include "eqeq12d.mm"
include "elab3.mm"
include "syl6bb.mm"
include "biadan2.mm"

theorem isghm
  let vv: setvar v
  let vu: setvar u
  let c.pl: class .+
  let c.pd: class .+^
  let cS: class S
  let cT: class T
  let cF: class F
  let cX: class X
  let cY: class Y
  let vs: setvar s
  let vt: setvar t
  let vw: setvar w
  let vf: setvar f
  assume isghm.w: |- X = ( Base ` S )
  assume isghm.x: |- Y = ( Base ` T )
  assume isghm.a: |- .+ = ( +g ` S )
  assume isghm.b: |- .+^ = ( +g ` T )

  disjoint u v
  disjoint S u
  disjoint S v
  disjoint T u
  disjoint T v
  disjoint X u
  disjoint X v
  disjoint .+ u
  disjoint .+ v
  disjoint Y u
  disjoint Y v
  disjoint .+^ u
  disjoint .+^ v
  disjoint F u
  disjoint F v
  disjoint s t
  disjoint s w
  disjoint s u
  disjoint s v
  disjoint f s
  disjoint S s
  disjoint t w
  disjoint t u
  disjoint t v
  disjoint f t
  disjoint S t
  disjoint u w
  disjoint v w
  disjoint f w
  disjoint S w
  disjoint f u
  disjoint f v
  disjoint S f
  disjoint T s
  disjoint T t
  disjoint T w
  disjoint T f
  disjoint X f
  disjoint X t
  disjoint X s
  disjoint .+ f
  disjoint .+ s
  disjoint .+ t
  disjoint Y f
  disjoint Y s
  disjoint Y t
  disjoint .+^ f
  disjoint .+^ s
  disjoint .+^ t
  disjoint F f
  assert |- ( F e. ( S GrpHom T ) <-> ( ( S e. Grp /\ T e. Grp ) /\ ( F : X --> Y /\ A. u e. X A. v e. X ( F ` ( u .+ v ) ) = ( ( F ` u ) .+^ ( F ` v ) ) ) ) )

  proof
    cF
    cS
    cT
    cghm
    co
    #
    wcel
    #
    cS
    cgrp
    wcel
    cT
    cgrp
    wcel
    wa
    #
    cX
    cY
    cF
    wf
    #
    vu
    cv
    #
    vv
    cv
    #
    c.pl
    co
    #
    cF
    cfv
    #
    @4
    cF
    cfv
    #
    @5
    cF
    cfv
    #
    c.pd
    co
    #
    wceq
    #
    vv
    cX
    wral
    vu
    cX
    wral
    #
    wa
    #
    vs
    vt
    cgrp
    cgrp
    vw
    cv
    #
    vt
    cv
    #
    cbs
    cfv
    #
    vf
    cv
    #
    wf
    #
    @4
    @5
    vs
    cv
    #
    cplusg
    cfv
    #
    co
    #
    @17
    cfv
    #
    @4
    @17
    cfv
    #
    @5
    @17
    cfv
    #
    @15
    cplusg
    cfv
    #
    co
    #
    wceq
    #
    vv
    @14
    wral
    #
    vu
    @14
    wral
    #
    wa
    #
    vw
    @19
    cbs
    cfv
    #
    wsbc
    #
    vf
    cab
    #
    cS
    cT
    cghm
    cF
    vu
    vv
    vw
    vt
    vf
    vs
    df-ghm
    #
    elmpt2cl
    @2
    @1
    cF
    cX
    cY
    @17
    wf
    #
    @6
    @17
    cfv
    #
    @23
    @24
    c.pd
    co
    #
    wceq
    #
    vv
    cX
    wral
    vu
    cX
    wral
    #
    wa
    #
    vf
    cab
    #
    wcel
    @13
    @2
    @0
    @41
    cF
    vs
    vt
    cS
    cT
    cgrp
    cgrp
    @33
    @41
    cghm
    cX
    @16
    @17
    wf
    #
    @36
    @26
    wceq
    #
    vv
    cX
    wral
    #
    vu
    cX
    wral
    #
    wa
    #
    vf
    cab
    @19
    cS
    wceq
    #
    @32
    @46
    vf
    @32
    @31
    @16
    @17
    wf
    #
    @27
    vv
    @31
    wral
    #
    vu
    @31
    wral
    #
    wa
    #
    @47
    @46
    @30
    @51
    vw
    @31
    @19
    cbs
    fvex
    @14
    @31
    wceq
    @18
    @48
    @29
    @50
    @14
    @31
    @16
    @17
    feq2
    @28
    @49
    vu
    @14
    @31
    @27
    vv
    @14
    @31
    raleq
    raleqbi1dv
    anbi12d
    sbcie
    @47
    @48
    @42
    @50
    @45
    @47
    @31
    cX
    @16
    @17
    @47
    @31
    cS
    cbs
    cfv
    #
    cX
    @19
    cS
    cbs
    fveq2
    isghm.w
    syl6eqr
    #
    feq2d
    @47
    @49
    @44
    vu
    @31
    cX
    @53
    @47
    @27
    @43
    vv
    @31
    cX
    @53
    @47
    @22
    @36
    @26
    @47
    @21
    @6
    @17
    @47
    @20
    c.pl
    @4
    @5
    @47
    @20
    cS
    cplusg
    cfv
    c.pl
    @19
    cS
    cplusg
    fveq2
    isghm.a
    syl6eqr
    oveqd
    fveq2d
    eqeq1d
    raleqbidv
    raleqbidv
    anbi12d
    syl5bb
    abbidv
    @15
    cT
    wceq
    #
    @46
    @40
    vf
    @54
    @42
    @35
    @45
    @39
    @54
    @16
    cY
    @17
    cX
    @54
    @16
    cT
    cbs
    cfv
    #
    cY
    @15
    cT
    cbs
    fveq2
    isghm.x
    syl6eqr
    feq3d
    @54
    @43
    @38
    vu
    vv
    cX
    cX
    @54
    @26
    @37
    @36
    @54
    @25
    c.pd
    @23
    @24
    @54
    @25
    cT
    cplusg
    cfv
    c.pd
    @15
    cT
    cplusg
    fveq2
    isghm.b
    syl6eqr
    oveqd
    eqeq2d
    2ralbidv
    anbi12d
    abbidv
    @34
    @41
    @35
    vf
    cab
    #
    cX
    cvv
    wcel
    #
    cY
    cvv
    wcel
    @56
    cvv
    wcel
    cX
    @52
    cvv
    isghm.w
    cS
    cbs
    fvex
    eqeltri
    #
    cY
    @55
    cvv
    isghm.x
    cT
    cbs
    fvex
    eqeltri
    cX
    cY
    cvv
    cvv
    vf
    mapex
    mp2an
    @40
    @35
    vf
    @35
    @39
    simpl
    ss2abi
    ssexi
    ovmpt2
    eleq2d
    @40
    @13
    vf
    cF
    @3
    cF
    cvv
    wcel
    #
    @12
    @3
    @57
    @59
    @58
    cX
    cY
    cvv
    cF
    fex
    mpan2
    adantr
    @17
    cF
    wceq
    #
    @35
    @3
    @39
    @12
    cX
    cY
    @17
    cF
    feq1
    @60
    @38
    @11
    vu
    vv
    cX
    cX
    @60
    @36
    @7
    @37
    @10
    @6
    @17
    cF
    fveq1
    @60
    @23
    @8
    @24
    @9
    c.pd
    @4
    @17
    cF
    fveq1
    @5
    @17
    cF
    fveq1
    oveq12d
    eqeq12d
    2ralbidv
    anbi12d
    elab3
    syl6bb
    biadan2
end
