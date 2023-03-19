include "crg.mm"
include "wcel.mm"
include "wa.mm"
include "cplusg.mm"
include "cfv.mm"
include "cv.mm"
include "co.mm"
include "cmpt.mm"
include "eqid.mm"
include "cgrp.mm"
include "ringgrp.mm"
include "adantr.mm"
include "ringcl.mm"
include "3expa.mm"
include "fmptd.mm"
include "wceq.mm"
include "w3a.mm"
include "3anass.mm"
include "ringdi.mm"
include "sylan2br.mm"
include "anassrs.mm"
include "ringacl.mm"
include "3expb.mm"
include "adantlr.mm"
include "oveq2.mm"
include "ovex.mm"
include "fvmpt.mm"
include "syl.mm"
include "oveqan12d.mm"
include "adantl.mm"
include "3eqtr4d.mm"
include "isghmd.mm"

theorem ringlghm
  let vx: setvar x
  let cB: class B
  let cR: class R
  let c.x: class .x.
  let cX: class X
  let vy: setvar y
  let vz: setvar z
  assume ringlghm.b: |- B = ( Base ` R )
  assume ringlghm.t: |- .x. = ( .r ` R )

  disjoint B x
  disjoint R x
  disjoint .x. x
  disjoint X x
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint B y
  disjoint B z
  disjoint R y
  disjoint R z
  disjoint .x. y
  disjoint .x. z
  disjoint X y
  disjoint X z
  assert |- ( ( R e. Ring /\ X e. B ) -> ( x e. B |-> ( X .x. x ) ) e. ( R GrpHom R ) )

  proof
    cR
    crg
    wcel
    #
    cX
    cB
    wcel
    #
    wa
    #
    vy
    vz
    cR
    cplusg
    cfv
    #
    @3
    cR
    cR
    vx
    cB
    cX
    vx
    cv
    #
    c.x
    co
    #
    cmpt
    #
    cB
    cB
    ringlghm.b
    ringlghm.b
    @3
    eqid
    #
    @7
    @0
    cR
    cgrp
    wcel
    @1
    cR
    ringgrp
    adantr
    #
    @8
    @2
    vx
    cB
    @5
    cB
    @6
    @0
    @1
    @4
    cB
    wcel
    @5
    cB
    wcel
    cB
    cR
    c.x
    cX
    @4
    ringlghm.b
    ringlghm.t
    ringcl
    3expa
    @6
    eqid
    #
    fmptd
    @2
    vy
    cv
    #
    cB
    wcel
    #
    vz
    cv
    #
    cB
    wcel
    #
    wa
    #
    wa
    #
    cX
    @10
    @12
    @3
    co
    #
    c.x
    co
    #
    cX
    @10
    c.x
    co
    #
    cX
    @12
    c.x
    co
    #
    @3
    co
    #
    @16
    @6
    cfv
    #
    @10
    @6
    cfv
    #
    @12
    @6
    cfv
    #
    @3
    co
    #
    @0
    @1
    @14
    @17
    @20
    wceq
    #
    @1
    @14
    wa
    @0
    @1
    @11
    @13
    w3a
    @25
    @1
    @11
    @13
    3anass
    cB
    @3
    cR
    c.x
    cX
    @10
    @12
    ringlghm.b
    @7
    ringlghm.t
    ringdi
    sylan2br
    anassrs
    @15
    @16
    cB
    wcel
    #
    @21
    @17
    wceq
    @0
    @14
    @26
    @1
    @0
    @11
    @13
    @26
    cB
    @3
    cR
    @10
    @12
    ringlghm.b
    @7
    ringacl
    3expb
    adantlr
    vx
    @16
    @5
    @17
    cB
    @6
    @4
    @16
    cX
    c.x
    oveq2
    @9
    cX
    @16
    c.x
    ovex
    fvmpt
    syl
    @14
    @24
    @20
    wceq
    @2
    @11
    @13
    @22
    @18
    @23
    @19
    @3
    vx
    @10
    @5
    @18
    cB
    @6
    @4
    @10
    cX
    c.x
    oveq2
    @9
    cX
    @10
    c.x
    ovex
    fvmpt
    vx
    @12
    @5
    @19
    cB
    @6
    @4
    @12
    cX
    c.x
    oveq2
    @9
    cX
    @12
    c.x
    ovex
    fvmpt
    oveqan12d
    adantl
    3eqtr4d
    isghmd
end
