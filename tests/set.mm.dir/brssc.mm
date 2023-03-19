include "cssc.mm"
include "wbr.mm"
include "cvv.mm"
include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "cxp.mm"
include "wfn.mm"
include "cfv.mm"
include "cpw.mm"
include "cixp.mm"
include "wrex.mm"
include "wex.mm"
include "wrel.mm"
include "sscrel.mm"
include "brrelex12.mm"
include "mpan.mm"
include "vex.mm"
include "xpex.mm"
include "fnex.mm"
include "mpan2.mm"
include "elex.mm"
include "rexlimivw.mm"
include "anim12ci.mm"
include "exlimiv.mm"
include "wceq.mm"
include "simpr.mm"
include "fneq1d.mm"
include "simpl.mm"
include "fveq1d.mm"
include "pweqd.mm"
include "ixpeq2dv.mm"
include "eleq12d.mm"
include "rexbidv.mm"
include "anbi12d.mm"
include "exbidv.mm"
include "df-ssc.mm"
include "brabga.mm"
include "pm5.21nii.mm"

theorem brssc
  let vx: setvar x
  let vt: setvar t
  let cH: class H
  let cJ: class J
  let vs: setvar s
  let vc: setvar c
  let vf: setvar f
  let vg: setvar g
  let vh: setvar h
  let vj: setvar j
  let vy: setvar y
  let vz: setvar z

  disjoint s t
  disjoint s x
  disjoint t x
  disjoint H s
  disjoint H t
  disjoint H x
  disjoint J s
  disjoint J t
  disjoint J x
  disjoint c f
  disjoint c g
  disjoint c h
  disjoint c j
  disjoint c s
  disjoint c t
  disjoint c x
  disjoint c y
  disjoint c z
  disjoint f g
  disjoint f h
  disjoint f j
  disjoint f s
  disjoint f t
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint g h
  disjoint g j
  disjoint g s
  disjoint g t
  disjoint g x
  disjoint g y
  disjoint g z
  disjoint h j
  disjoint h s
  disjoint h t
  disjoint h x
  disjoint h y
  disjoint h z
  disjoint j s
  disjoint j t
  disjoint j x
  disjoint j y
  disjoint j z
  disjoint s y
  disjoint s z
  disjoint t y
  disjoint t z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint H h
  disjoint H j
  disjoint J h
  disjoint J j
  assert |- ( H C_cat J <-> E. t ( J Fn ( t X. t ) /\ E. s e. ~P t H e. X_ x e. ( s X. s ) ~P ( J ` x ) ) )

  proof
    cH
    cJ
    cssc
    wbr
    #
    cH
    cvv
    wcel
    #
    cJ
    cvv
    wcel
    #
    wa
    #
    cJ
    vt
    cv
    #
    @4
    cxp
    #
    wfn
    #
    cH
    vx
    vs
    cv
    #
    @7
    cxp
    #
    vx
    cv
    #
    cJ
    cfv
    #
    cpw
    #
    cixp
    #
    wcel
    #
    vs
    @4
    cpw
    #
    wrex
    #
    wa
    #
    vt
    wex
    #
    cssc
    wrel
    @0
    @3
    sscrel
    cH
    cJ
    cssc
    brrelex12
    mpan
    @16
    @3
    vt
    @6
    @2
    @15
    @1
    @6
    @5
    cvv
    wcel
    @2
    @4
    @4
    vt
    vex
    #
    @18
    xpex
    @5
    cvv
    cJ
    fnex
    mpan2
    @13
    @1
    vs
    @14
    cH
    @12
    elex
    rexlimivw
    anim12ci
    exlimiv
    vj
    cv
    #
    @5
    wfn
    #
    vh
    cv
    #
    vx
    @8
    @9
    @19
    cfv
    #
    cpw
    #
    cixp
    #
    wcel
    #
    vs
    @14
    wrex
    #
    wa
    #
    vt
    wex
    @17
    vh
    vj
    cH
    cJ
    cssc
    cvv
    cvv
    @21
    cH
    wceq
    #
    @19
    cJ
    wceq
    #
    wa
    #
    @27
    @16
    vt
    @30
    @20
    @6
    @26
    @15
    @30
    @5
    @19
    cJ
    @28
    @29
    simpr
    #
    fneq1d
    @30
    @25
    @13
    vs
    @14
    @30
    @21
    cH
    @24
    @12
    @28
    @29
    simpl
    @30
    vx
    @8
    @23
    @11
    @30
    @22
    @10
    @30
    @9
    @19
    cJ
    @31
    fveq1d
    pweqd
    ixpeq2dv
    eleq12d
    rexbidv
    anbi12d
    exbidv
    vx
    vt
    vh
    vj
    vs
    df-ssc
    brabga
    pm5.21nii
end
