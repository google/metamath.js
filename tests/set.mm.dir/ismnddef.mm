include "cv.mm"
include "co.mm"
include "wceq.mm"
include "wa.mm"
include "wral.mm"
include "wrex.mm"
include "cplusg.mm"
include "cfv.mm"
include "wsbc.mm"
include "cbs.mm"
include "csgrp.mm"
include "cmnd.mm"
include "fvex.mm"
include "wb.mm"
include "fveq2.mm"
include "syl6eqr.mm"
include "eqeq2d.mm"
include "anbi12d.mm"
include "simpl.mm"
include "oveq.mm"
include "eqeq1d.mm"
include "adantl.mm"
include "raleqbidv.mm"
include "rexeqbidv.mm"
include "syl6bi.mm"
include "sbc2iedv.mm"
include "df-mnd.mm"
include "elrab2.mm"

theorem ismnddef
  let cB: class B
  let c.pl: class .+
  let ve: setvar e
  let cG: class G
  let va: setvar a
  let vb: setvar b
  let vg: setvar g
  let vp: setvar p
  assume ismnddef.b: |- B = ( Base ` G )
  assume ismnddef.p: |- .+ = ( +g ` G )

  disjoint B a
  disjoint B e
  disjoint a e
  disjoint .+ a
  disjoint .+ e
  disjoint B b
  disjoint B g
  disjoint B p
  disjoint a b
  disjoint a g
  disjoint a p
  disjoint b e
  disjoint b g
  disjoint b p
  disjoint e g
  disjoint e p
  disjoint g p
  disjoint G b
  disjoint G g
  disjoint G p
  disjoint .+ b
  disjoint .+ g
  disjoint .+ p
  assert |- ( G e. Mnd <-> ( G e. SGrp /\ E. e e. B A. a e. B ( ( e .+ a ) = a /\ ( a .+ e ) = a ) ) )

  proof
    ve
    cv
    #
    va
    cv
    #
    vp
    cv
    #
    co
    #
    @1
    wceq
    #
    @1
    @0
    @2
    co
    #
    @1
    wceq
    #
    wa
    #
    va
    vb
    cv
    #
    wral
    #
    ve
    @8
    wrex
    #
    vp
    vg
    cv
    #
    cplusg
    cfv
    #
    wsbc
    vb
    @11
    cbs
    cfv
    #
    wsbc
    @0
    @1
    c.pl
    co
    #
    @1
    wceq
    #
    @1
    @0
    c.pl
    co
    #
    @1
    wceq
    #
    wa
    #
    va
    cB
    wral
    #
    ve
    cB
    wrex
    #
    vg
    cG
    csgrp
    cmnd
    @11
    cG
    wceq
    #
    @10
    @20
    vb
    vp
    @13
    @12
    @11
    cbs
    fvex
    @11
    cplusg
    fvex
    @21
    @8
    @13
    wceq
    #
    @2
    @12
    wceq
    #
    wa
    @8
    cB
    wceq
    #
    @2
    c.pl
    wceq
    #
    wa
    #
    @10
    @20
    wb
    @21
    @22
    @24
    @23
    @25
    @21
    @13
    cB
    @8
    @21
    @13
    cG
    cbs
    cfv
    cB
    @11
    cG
    cbs
    fveq2
    ismnddef.b
    syl6eqr
    eqeq2d
    @21
    @12
    c.pl
    @2
    @21
    @12
    cG
    cplusg
    cfv
    c.pl
    @11
    cG
    cplusg
    fveq2
    ismnddef.p
    syl6eqr
    eqeq2d
    anbi12d
    @26
    @9
    @19
    ve
    @8
    cB
    @24
    @25
    simpl
    #
    @26
    @7
    @18
    va
    @8
    cB
    @27
    @25
    @7
    @18
    wb
    @24
    @25
    @4
    @15
    @6
    @17
    @25
    @3
    @14
    @1
    @0
    @1
    @2
    c.pl
    oveq
    eqeq1d
    @25
    @5
    @16
    @1
    @1
    @0
    @2
    c.pl
    oveq
    eqeq1d
    anbi12d
    adantl
    raleqbidv
    rexeqbidv
    syl6bi
    sbc2iedv
    va
    ve
    vg
    vp
    vb
    df-mnd
    elrab2
end
