include "wcel.mm"
include "wa.mm"
include "ctgrp.mm"
include "cfv.mm"
include "cnx.mm"
include "cbs.mm"
include "cop.mm"
include "cplusg.mm"
include "cv.mm"
include "ccom.mm"
include "cmpt2.mm"
include "cpr.mm"
include "cltrn.mm"
include "cmpt.mm"
include "tgrpfset.mm"
include "fveq1d.mm"
include "wceq.mm"
include "fveq2.mm"
include "opeq2d.mm"
include "eqidd.mm"
include "mpt2eq123dv.mm"
include "preq12d.mm"
include "eqid.mm"
include "prex.mm"
include "fvmpt.mm"
include "opeq2i.mm"
include "mpt2eq123i.mm"
include "preq12i.mm"
include "syl6eqr.mm"
include "sylan9eq.mm"
include "syl5eq.mm"

theorem tgrpset
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
  let c.pl: class .+
  let vk: setvar k
  let vw: setvar w
  let cB: class B
  let cX: class X
  let cY: class Y
  assume tgrpset.h: |- H = ( LHyp ` K )
  assume tgrpset.t: |- T = ( ( LTrn ` K ) ` W )
  assume tgrpset.g: |- G = ( ( TGrp ` K ) ` W )

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
  assert |- ( ( K e. V /\ W e. H ) -> G = { <. ( Base ` ndx ) , T >. , <. ( +g ` ndx ) , ( f e. T , g e. T |-> ( f o. g ) ) >. } )

  proof
    cK
    cV
    wcel
    #
    cW
    cH
    wcel
    #
    wa
    cG
    cW
    cK
    ctgrp
    cfv
    #
    cfv
    #
    cnx
    cbs
    cfv
    #
    cT
    cop
    #
    cnx
    cplusg
    cfv
    #
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
    #
    cpr
    #
    tgrpset.g
    @0
    @1
    @3
    cW
    vw
    cH
    @4
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
    @6
    vf
    vg
    @13
    @13
    @7
    cmpt2
    #
    cop
    #
    cpr
    #
    cmpt
    #
    cfv
    #
    @10
    @0
    cW
    @2
    @18
    vw
    vf
    vg
    cH
    cK
    cV
    tgrpset.h
    tgrpfset
    fveq1d
    @1
    @19
    @4
    cW
    @12
    cfv
    #
    cop
    #
    @6
    vf
    vg
    @20
    @20
    @7
    cmpt2
    #
    cop
    #
    cpr
    #
    @10
    vw
    cW
    @17
    @24
    cH
    @18
    @11
    cW
    wceq
    #
    @14
    @21
    @16
    @23
    @25
    @13
    @20
    @4
    @11
    cW
    @12
    fveq2
    #
    opeq2d
    @25
    @15
    @22
    @6
    @25
    vf
    vg
    @13
    @13
    @7
    @20
    @20
    @7
    @26
    @26
    @25
    @7
    eqidd
    mpt2eq123dv
    opeq2d
    preq12d
    @18
    eqid
    @21
    @23
    prex
    fvmpt
    @5
    @21
    @9
    @23
    cT
    @20
    @4
    tgrpset.t
    opeq2i
    @8
    @22
    @6
    vf
    vg
    cT
    cT
    @7
    @20
    @20
    @7
    tgrpset.t
    tgrpset.t
    @7
    eqid
    mpt2eq123i
    opeq2i
    preq12i
    syl6eqr
    sylan9eq
    syl5eq
end
