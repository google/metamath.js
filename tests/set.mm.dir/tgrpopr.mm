include "wcel.mm"
include "wa.mm"
include "cplusg.mm"
include "cfv.mm"
include "cnx.mm"
include "cbs.mm"
include "cop.mm"
include "cv.mm"
include "ccom.mm"
include "cmpt2.mm"
include "cpr.mm"
include "tgrpset.mm"
include "fveq2d.mm"
include "cvv.mm"
include "wceq.mm"
include "cltrn.mm"
include "fvex.mm"
include "eqeltri.mm"
include "mpt2ex.mm"
include "eqid.mm"
include "grpplusg.mm"
include "ax-mp.mm"
include "3eqtr4g.mm"

theorem tgrpopr
  let c.pl: class .+
  let cT: class T
  let vf: setvar f
  let vg: setvar g
  let cG: class G
  let cH: class H
  let cK: class K
  let cV: class V
  let cW: class W
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vk: setvar k
  let vw: setvar w
  let cB: class B
  let cX: class X
  let cY: class Y
  assume tgrpset.h: |- H = ( LHyp ` K )
  assume tgrpset.t: |- T = ( ( LTrn ` K ) ` W )
  assume tgrpset.g: |- G = ( ( TGrp ` K ) ` W )
  assume tgrp.o: |- .+ = ( +g ` G )

  disjoint f g
  disjoint K f
  disjoint K g
  disjoint T f
  disjoint T g
  disjoint W f
  disjoint W g
  disjoint x y
  disjoint x z
  disjoint .+ x
  disjoint y z
  disjoint .+ y
  disjoint .+ z
  disjoint k w
  disjoint k x
  disjoint k y
  disjoint k z
  disjoint H k
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint H w
  disjoint H x
  disjoint H y
  disjoint H z
  disjoint f k
  disjoint f w
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint g k
  disjoint g w
  disjoint g x
  disjoint g y
  disjoint g z
  disjoint K k
  disjoint K w
  disjoint K x
  disjoint K y
  disjoint K z
  disjoint T x
  disjoint T y
  disjoint T z
  disjoint B x
  disjoint B y
  disjoint B z
  disjoint G x
  disjoint G y
  disjoint G z
  disjoint W w
  disjoint W x
  disjoint W y
  disjoint W z
  disjoint X f
  disjoint X g
  disjoint Y f
  disjoint Y g
  assert |- ( ( K e. V /\ W e. H ) -> .+ = ( f e. T , g e. T |-> ( f o. g ) ) )

  proof
    cK
    cV
    wcel
    cW
    cH
    wcel
    wa
    #
    cG
    cplusg
    cfv
    cnx
    cbs
    cfv
    cT
    cop
    cnx
    cplusg
    cfv
    vf
    vg
    cT
    cT
    vf
    cv
    vg
    cv
    ccom
    #
    cmpt2
    #
    cop
    cpr
    #
    cplusg
    cfv
    #
    c.pl
    @2
    @0
    cG
    @3
    cplusg
    cT
    vf
    vg
    cG
    cH
    cK
    cV
    cW
    tgrpset.h
    tgrpset.t
    tgrpset.g
    tgrpset
    fveq2d
    tgrp.o
    @2
    cvv
    wcel
    @2
    @4
    wceq
    vf
    vg
    cT
    cT
    @1
    cT
    cW
    cK
    cltrn
    cfv
    #
    cfv
    cvv
    tgrpset.t
    cW
    @5
    fvex
    eqeltri
    #
    @6
    mpt2ex
    cT
    @2
    @3
    cvv
    @3
    eqid
    grpplusg
    ax-mp
    3eqtr4g
end
