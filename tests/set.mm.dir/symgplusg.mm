include "cvv.mm"
include "wcel.mm"
include "cv.mm"
include "ccom.mm"
include "cmpt2.mm"
include "wceq.mm"
include "cplusg.mm"
include "cfv.mm"
include "cnx.mm"
include "cbs.mm"
include "cop.mm"
include "cts.mm"
include "cpw.mm"
include "csn.mm"
include "cxp.mm"
include "cpt.mm"
include "ctp.mm"
include "symgbas.mm"
include "eqid.mm"
include "symgval.mm"
include "fveq2d.mm"
include "fvex.mm"
include "eqeltri.mm"
include "mpt2ex.mm"
include "topgrpplusg.mm"
include "ax-mp.mm"
include "3eqtr4g.mm"
include "wn.mm"
include "c0.mm"
include "csymg.mm"
include "fvprc.mm"
include "syl5eq.mm"
include "plusgid.mm"
include "str0.mm"
include "wfn.mm"
include "vex.mm"
include "coex.mm"
include "fnmpt2i.mm"
include "base0.mm"
include "xpeq2d.mm"
include "xp0.mm"
include "syl6eq.mm"
include "fneq2d.mm"
include "mpbii.mm"
include "fn0.mm"
include "sylib.mm"
include "eqtr4d.mm"
include "pm2.61i.mm"

theorem symgplusg
  let cA: class A
  let cB: class B
  let c.pl: class .+
  let vf: setvar f
  let vg: setvar g
  let cG: class G
  let vx: setvar x
  let cX: class X
  let cY: class Y
  assume symgplusg.1: |- G = ( SymGrp ` A )
  assume symgplusg.2: |- B = ( Base ` G )
  assume symgplusg.3: |- .+ = ( +g ` G )

  disjoint f g
  disjoint A f
  disjoint A g
  disjoint B f
  disjoint B g
  disjoint f x
  disjoint g x
  disjoint A x
  disjoint X f
  disjoint X g
  disjoint Y f
  disjoint Y g
  assert |- .+ = ( f e. B , g e. B |-> ( f o. g ) )

  proof
    cA
    cvv
    wcel
    #
    c.pl
    vf
    vg
    cB
    cB
    vf
    cv
    #
    vg
    cv
    #
    ccom
    #
    cmpt2
    #
    wceq
    @0
    cG
    cplusg
    cfv
    #
    cnx
    cbs
    cfv
    cB
    cop
    cnx
    cplusg
    cfv
    #
    @4
    cop
    cnx
    cts
    cfv
    cA
    cA
    cpw
    csn
    cxp
    cpt
    cfv
    #
    cop
    ctp
    #
    cplusg
    cfv
    #
    c.pl
    @4
    @0
    cG
    @8
    cplusg
    vx
    cA
    cB
    @4
    vf
    vg
    cG
    @7
    cvv
    symgplusg.1
    vx
    cA
    cB
    cG
    symgplusg.1
    symgplusg.2
    symgbas
    @4
    eqid
    #
    @7
    eqid
    symgval
    fveq2d
    symgplusg.3
    @4
    cvv
    wcel
    @4
    @9
    wceq
    vf
    vg
    cB
    cB
    @3
    cB
    cG
    cbs
    cfv
    #
    cvv
    symgplusg.2
    cG
    cbs
    fvex
    eqeltri
    #
    @12
    mpt2ex
    cB
    @4
    @7
    @8
    cvv
    @8
    eqid
    topgrpplusg
    ax-mp
    3eqtr4g
    @0
    wn
    #
    c.pl
    c0
    @4
    @13
    @5
    c0
    cplusg
    cfv
    c.pl
    c0
    @13
    cG
    c0
    cplusg
    @13
    cG
    cA
    csymg
    cfv
    c0
    symgplusg.1
    cA
    csymg
    fvprc
    syl5eq
    #
    fveq2d
    symgplusg.3
    cplusg
    @6
    plusgid
    str0
    3eqtr4g
    @13
    @4
    c0
    wfn
    #
    @4
    c0
    wceq
    @13
    @4
    cB
    cB
    cxp
    #
    wfn
    @15
    vf
    vg
    cB
    cB
    @3
    @4
    @10
    @1
    @2
    vf
    vex
    vg
    vex
    coex
    fnmpt2i
    @13
    @16
    c0
    @4
    @13
    @16
    cB
    c0
    cxp
    c0
    @13
    cB
    c0
    cB
    @13
    @11
    c0
    cbs
    cfv
    cB
    c0
    @13
    cG
    c0
    cbs
    @14
    fveq2d
    symgplusg.2
    base0
    3eqtr4g
    xpeq2d
    cB
    xp0
    syl6eq
    fneq2d
    mpbii
    @4
    fn0
    sylib
    eqtr4d
    pm2.61i
end
