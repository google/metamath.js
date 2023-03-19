include "wcel.mm"
include "cvv.mm"
include "ctgrp.mm"
include "cfv.mm"
include "cnx.mm"
include "cbs.mm"
include "cv.mm"
include "cltrn.mm"
include "cop.mm"
include "cplusg.mm"
include "ccom.mm"
include "cmpt2.mm"
include "cpr.mm"
include "cmpt.mm"
include "wceq.mm"
include "elex.mm"
include "clh.mm"
include "fveq2.mm"
include "syl6eqr.mm"
include "fveq1d.mm"
include "opeq2d.mm"
include "eqidd.mm"
include "mpt2eq123dv.mm"
include "preq12d.mm"
include "mpteq12dv.mm"
include "df-tgrp.mm"
include "fvex.mm"
include "eqeltri.mm"
include "mptex.mm"
include "fvmpt.mm"
include "syl.mm"

theorem tgrpfset
  let vw: setvar w
  let vf: setvar f
  let vg: setvar g
  let cH: class H
  let cK: class K
  let cV: class V
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let c.pl: class .+
  let vk: setvar k
  let cT: class T
  let cB: class B
  let cG: class G
  let cW: class W
  let cX: class X
  let cY: class Y
  assume tgrpset.h: |- H = ( LHyp ` K )

  disjoint H w
  disjoint f g
  disjoint f w
  disjoint K f
  disjoint g w
  disjoint K g
  disjoint K w
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
  disjoint H x
  disjoint H y
  disjoint H z
  disjoint f k
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint g k
  disjoint g x
  disjoint g y
  disjoint g z
  disjoint K k
  disjoint K x
  disjoint K y
  disjoint K z
  disjoint T f
  disjoint T g
  disjoint T x
  disjoint T y
  disjoint T z
  disjoint B x
  disjoint B y
  disjoint B z
  disjoint G x
  disjoint G y
  disjoint G z
  disjoint W f
  disjoint W g
  disjoint W w
  disjoint W x
  disjoint W y
  disjoint W z
  disjoint X f
  disjoint X g
  disjoint Y f
  disjoint Y g
  assert |- ( K e. V -> ( TGrp ` K ) = ( w e. H |-> { <. ( Base ` ndx ) , ( ( LTrn ` K ) ` w ) >. , <. ( +g ` ndx ) , ( f e. ( ( LTrn ` K ) ` w ) , g e. ( ( LTrn ` K ) ` w ) |-> ( f o. g ) ) >. } ) )

  proof
    cK
    cV
    wcel
    cK
    cvv
    wcel
    cK
    ctgrp
    cfv
    vw
    cH
    cnx
    cbs
    cfv
    #
    vw
    cv
    #
    cK
    cltrn
    cfv
    #
    cfv
    #
    cop
    #
    cnx
    cplusg
    cfv
    #
    vf
    vg
    @3
    @3
    vf
    cv
    vg
    cv
    ccom
    #
    cmpt2
    #
    cop
    #
    cpr
    #
    cmpt
    #
    wceq
    cK
    cV
    elex
    vk
    cK
    vw
    vk
    cv
    #
    clh
    cfv
    #
    @0
    @1
    @11
    cltrn
    cfv
    #
    cfv
    #
    cop
    #
    @5
    vf
    vg
    @14
    @14
    @6
    cmpt2
    #
    cop
    #
    cpr
    #
    cmpt
    @10
    cvv
    ctgrp
    @11
    cK
    wceq
    #
    vw
    @12
    @18
    cH
    @9
    @19
    @12
    cK
    clh
    cfv
    #
    cH
    @11
    cK
    clh
    fveq2
    tgrpset.h
    syl6eqr
    @19
    @15
    @4
    @17
    @8
    @19
    @14
    @3
    @0
    @19
    @1
    @13
    @2
    @11
    cK
    cltrn
    fveq2
    fveq1d
    #
    opeq2d
    @19
    @16
    @7
    @5
    @19
    vf
    vg
    @14
    @14
    @6
    @3
    @3
    @6
    @21
    @21
    @19
    @6
    eqidd
    mpt2eq123dv
    opeq2d
    preq12d
    mpteq12dv
    vw
    vf
    vg
    vk
    df-tgrp
    vw
    cH
    @9
    cH
    @20
    cvv
    tgrpset.h
    cK
    clh
    fvex
    eqeltri
    mptex
    fvmpt
    syl
end
