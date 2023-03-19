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
include "an32s.mm"
include "fmptd.mm"
include "wceq.mm"
include "w3a.mm"
include "df-3an.mm"
include "ringdir.mm"
include "sylan2br.mm"
include "anass1rs.mm"
include "ringacl.mm"
include "3expb.mm"
include "adantlr.mm"
include "oveq1.mm"
include "ovex.mm"
include "fvmpt.mm"
include "syl.mm"
include "oveqan12d.mm"
include "adantl.mm"
include "3eqtr4d.mm"
include "isghmd.mm"

theorem ringrghm
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
  assert |- ( ( R e. Ring /\ X e. B ) -> ( x e. B |-> ( x .x. X ) ) e. ( R GrpHom R ) )

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
    vx
    cv
    #
    cX
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
    @4
    cB
    wcel
    #
    @1
    @5
    cB
    wcel
    #
    @0
    @9
    @1
    @10
    cB
    cR
    c.x
    @4
    cX
    ringlghm.b
    ringlghm.t
    ringcl
    3expa
    an32s
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
    @12
    @14
    @3
    co
    #
    cX
    c.x
    co
    #
    @12
    cX
    c.x
    co
    #
    @14
    cX
    c.x
    co
    #
    @3
    co
    #
    @18
    @6
    cfv
    #
    @12
    @6
    cfv
    #
    @14
    @6
    cfv
    #
    @3
    co
    #
    @0
    @16
    @1
    @19
    @22
    wceq
    #
    @16
    @1
    wa
    @0
    @13
    @15
    @1
    w3a
    @27
    @13
    @15
    @1
    df-3an
    cB
    @3
    cR
    c.x
    @12
    @14
    cX
    ringlghm.b
    @7
    ringlghm.t
    ringdir
    sylan2br
    anass1rs
    @17
    @18
    cB
    wcel
    #
    @23
    @19
    wceq
    @0
    @16
    @28
    @1
    @0
    @13
    @15
    @28
    cB
    @3
    cR
    @12
    @14
    ringlghm.b
    @7
    ringacl
    3expb
    adantlr
    vx
    @18
    @5
    @19
    cB
    @6
    @4
    @18
    cX
    c.x
    oveq1
    @11
    @18
    cX
    c.x
    ovex
    fvmpt
    syl
    @16
    @26
    @22
    wceq
    @2
    @13
    @15
    @24
    @20
    @25
    @21
    @3
    vx
    @12
    @5
    @20
    cB
    @6
    @4
    @12
    cX
    c.x
    oveq1
    @11
    @12
    cX
    c.x
    ovex
    fvmpt
    vx
    @14
    @5
    @21
    cB
    @6
    @4
    @14
    cX
    c.x
    oveq1
    @11
    @14
    cX
    c.x
    ovex
    fvmpt
    oveqan12d
    adantl
    3eqtr4d
    isghmd
end
