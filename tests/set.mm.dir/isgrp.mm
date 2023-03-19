include "cv.mm"
include "cplusg.mm"
include "cfv.mm"
include "co.mm"
include "c0g.mm"
include "wceq.mm"
include "cbs.mm"
include "wrex.mm"
include "wral.mm"
include "cmnd.mm"
include "cgrp.mm"
include "fveq2.mm"
include "syl6eqr.mm"
include "oveqd.mm"
include "eqeq12d.mm"
include "rexeqbidv.mm"
include "raleqbidv.mm"
include "df-grp.mm"
include "elrab2.mm"

theorem isgrp
  let cB: class B
  let c.pl: class .+
  let vm: setvar m
  let cG: class G
  let c.0: class .0.
  let va: setvar a
  let vg: setvar g
  assume isgrp.b: |- B = ( Base ` G )
  assume isgrp.p: |- .+ = ( +g ` G )
  assume isgrp.z: |- .0. = ( 0g ` G )

  disjoint a m
  disjoint B a
  disjoint B m
  disjoint G a
  disjoint G m
  disjoint a g
  disjoint g m
  disjoint B g
  disjoint G g
  disjoint .+ g
  disjoint .0. g
  assert |- ( G e. Grp <-> ( G e. Mnd /\ A. a e. B E. m e. B ( m .+ a ) = .0. ) )

  proof
    vm
    cv
    #
    va
    cv
    #
    vg
    cv
    #
    cplusg
    cfv
    #
    co
    #
    @2
    c0g
    cfv
    #
    wceq
    #
    vm
    @2
    cbs
    cfv
    #
    wrex
    #
    va
    @7
    wral
    @0
    @1
    c.pl
    co
    #
    c.0
    wceq
    #
    vm
    cB
    wrex
    #
    va
    cB
    wral
    vg
    cG
    cmnd
    cgrp
    @2
    cG
    wceq
    #
    @8
    @11
    va
    @7
    cB
    @12
    @7
    cG
    cbs
    cfv
    cB
    @2
    cG
    cbs
    fveq2
    isgrp.b
    syl6eqr
    #
    @12
    @6
    @10
    vm
    @7
    cB
    @13
    @12
    @4
    @9
    @5
    c.0
    @12
    @3
    c.pl
    @0
    @1
    @12
    @3
    cG
    cplusg
    cfv
    c.pl
    @2
    cG
    cplusg
    fveq2
    isgrp.p
    syl6eqr
    oveqd
    @12
    @5
    cG
    c0g
    cfv
    c.0
    @2
    cG
    c0g
    fveq2
    isgrp.z
    syl6eqr
    eqeq12d
    rexeqbidv
    raleqbidv
    vg
    vm
    va
    df-grp
    elrab2
end
