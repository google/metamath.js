include "cgrp.mm"
include "wcel.mm"
include "wa.mm"
include "cfv.mm"
include "cz.mm"
include "cv.mm"
include "co.mm"
include "cmpt.mm"
include "crn.mm"
include "cfn.mm"
include "chash.mm"
include "cc0.mm"
include "cif.mm"
include "wceq.mm"
include "iscyggen.mm"
include "simplbi.mm"
include "eqid.mm"
include "dfod2.mm"
include "sylan2.mm"
include "simprbi.mm"
include "adantl.mm"
include "eleq1d.mm"
include "fveq2d.mm"
include "ifbieq1d.mm"
include "eqtrd.mm"

theorem cyggenod2
  let vx: setvar x
  let cB: class B
  let c.x: class .x.
  let vn: setvar n
  let cE: class E
  let cG: class G
  let cO: class O
  let cX: class X
  let vg: setvar g
  let vm: setvar m
  let vy: setvar y
  let cN: class N
  let wph: wff ph
  assume iscyg.1: |- B = ( Base ` G )
  assume iscyg.2: |- .x. = ( .g ` G )
  assume iscyg3.e: |- E = { x e. B | ran ( n e. ZZ |-> ( n .x. x ) ) = B }
  assume cyggenod.o: |- O = ( od ` G )

  disjoint n x
  disjoint B n
  disjoint B x
  disjoint O n
  disjoint X n
  disjoint X x
  disjoint G n
  disjoint G x
  disjoint .x. n
  disjoint .x. x
  disjoint g m
  disjoint g n
  disjoint g x
  disjoint g y
  disjoint B g
  disjoint m n
  disjoint m x
  disjoint m y
  disjoint B m
  disjoint n y
  disjoint x y
  disjoint B y
  disjoint E m
  disjoint E y
  disjoint N m
  disjoint N n
  disjoint N x
  disjoint N y
  disjoint X m
  disjoint X y
  disjoint G g
  disjoint G m
  disjoint G y
  disjoint ph y
  disjoint .x. g
  disjoint .x. m
  disjoint .x. y
  assert |- ( ( G e. Grp /\ X e. E ) -> ( O ` X ) = if ( B e. Fin , ( # ` B ) , 0 ) )

  proof
    cG
    cgrp
    wcel
    #
    cX
    cE
    wcel
    #
    wa
    #
    cX
    cO
    cfv
    #
    vn
    cz
    vn
    cv
    cX
    c.x
    co
    cmpt
    #
    crn
    #
    cfn
    wcel
    #
    @5
    chash
    cfv
    #
    cc0
    cif
    #
    cB
    cfn
    wcel
    #
    cB
    chash
    cfv
    #
    cc0
    cif
    @1
    @0
    cX
    cB
    wcel
    #
    @3
    @8
    wceq
    @1
    @11
    @5
    cB
    wceq
    #
    vx
    cB
    c.x
    vn
    cE
    cG
    cX
    iscyg.1
    iscyg.2
    iscyg3.e
    iscyggen
    #
    simplbi
    vn
    cX
    c.x
    @4
    cG
    cO
    cB
    iscyg.1
    cyggenod.o
    iscyg.2
    @4
    eqid
    dfod2
    sylan2
    @2
    @6
    @9
    @7
    @10
    cc0
    @2
    @5
    cB
    cfn
    @1
    @12
    @0
    @1
    @11
    @12
    @13
    simprbi
    adantl
    #
    eleq1d
    @2
    @5
    cB
    chash
    @14
    fveq2d
    ifbieq1d
    eqtrd
end
