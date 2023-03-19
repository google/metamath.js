include "wcel.mm"
include "wa.mm"
include "cbs.mm"
include "cfv.mm"
include "cnx.mm"
include "cop.mm"
include "cplusg.mm"
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
include "eqid.mm"
include "grpbase.mm"
include "ax-mp.mm"
include "3eqtr4g.mm"

theorem tgrpbase
  let cC: class C
  let cT: class T
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
  let vf: setvar f
  let vg: setvar g
  let cB: class B
  let cX: class X
  let cY: class Y
  assume tgrpset.h: |- H = ( LHyp ` K )
  assume tgrpset.t: |- T = ( ( LTrn ` K ) ` W )
  assume tgrpset.g: |- G = ( ( TGrp ` K ) ` W )
  assume tgrp.c: |- C = ( Base ` G )


  assert |- ( ( K e. V /\ W e. H ) -> C = T )

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
    cbs
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
    cmpt2
    #
    cop
    cpr
    #
    cbs
    cfv
    #
    cC
    cT
    @0
    cG
    @2
    cbs
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
    tgrp.c
    cT
    cvv
    wcel
    cT
    @3
    wceq
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
    @4
    fvex
    eqeltri
    cT
    @1
    @2
    cvv
    @2
    eqid
    grpbase
    ax-mp
    3eqtr4g
end
