include "cgrp.mm"
include "wcel.mm"
include "wa.mm"
include "zring.mm"
include "cz.mm"
include "wf.mm"
include "cv.mm"
include "caddc.mm"
include "co.mm"
include "cfv.mm"
include "cplusg.mm"
include "wceq.mm"
include "wral.mm"
include "cghm.mm"
include "simpl.mm"
include "zringgrp.mm"
include "jctil.mm"
include "mulgcl.mm"
include "3expa.mm"
include "an32s.mm"
include "fmptd.mm"
include "eqid.mm"
include "mulgdir.mm"
include "3exp2.mm"
include "imp42.mm"
include "zaddcl.mm"
include "adantl.mm"
include "oveq1.mm"
include "ovex.mm"
include "fvmpt.mm"
include "syl.mm"
include "oveqan12d.mm"
include "3eqtr4d.mm"
include "ralrimivva.mm"
include "jca.mm"
include "zringbas.mm"
include "zringplusg.mm"
include "isghm.mm"
include "sylanbrc.mm"

theorem mulgghm2
  let cB: class B
  let cR: class R
  let c.x: class .x.
  let c.1: class .1.
  let vn: setvar n
  let cF: class F
  let vx: setvar x
  let vy: setvar y
  let vf: setvar f
  assume mulgghm2.m: |- .x. = ( .g ` R )
  assume mulgghm2.f: |- F = ( n e. ZZ |-> ( n .x. .1. ) )
  assume mulgghm2.b: |- B = ( Base ` R )

  disjoint B n
  disjoint R n
  disjoint .x. n
  disjoint .1. n
  disjoint n x
  disjoint n y
  disjoint x y
  disjoint B x
  disjoint B y
  disjoint f x
  disjoint f y
  disjoint F f
  disjoint F x
  disjoint F y
  disjoint f n
  disjoint R f
  disjoint R x
  disjoint R y
  disjoint .1. x
  disjoint .1. y
  assert |- ( ( R e. Grp /\ .1. e. B ) -> F e. ( ZZring GrpHom R ) )

  proof
    cR
    cgrp
    wcel
    #
    c.1
    cB
    wcel
    #
    wa
    #
    zring
    cgrp
    wcel
    #
    @0
    wa
    cz
    cB
    cF
    wf
    #
    vx
    cv
    #
    vy
    cv
    #
    caddc
    co
    #
    cF
    cfv
    #
    @5
    cF
    cfv
    #
    @6
    cF
    cfv
    #
    cR
    cplusg
    cfv
    #
    co
    #
    wceq
    #
    vy
    cz
    wral
    vx
    cz
    wral
    #
    wa
    cF
    zring
    cR
    cghm
    co
    wcel
    @2
    @0
    @3
    @0
    @1
    simpl
    zringgrp
    jctil
    @2
    @4
    @14
    @2
    vn
    cz
    vn
    cv
    #
    c.1
    c.x
    co
    #
    cB
    cF
    @0
    @15
    cz
    wcel
    #
    @1
    @16
    cB
    wcel
    #
    @0
    @17
    @1
    @18
    cB
    c.x
    cR
    @15
    c.1
    mulgghm2.b
    mulgghm2.m
    mulgcl
    3expa
    an32s
    mulgghm2.f
    fmptd
    @2
    @13
    vx
    vy
    cz
    cz
    @2
    @5
    cz
    wcel
    #
    @6
    cz
    wcel
    #
    wa
    #
    wa
    #
    @7
    c.1
    c.x
    co
    #
    @5
    c.1
    c.x
    co
    #
    @6
    c.1
    c.x
    co
    #
    @11
    co
    #
    @8
    @12
    @0
    @21
    @1
    @23
    @26
    wceq
    #
    @0
    @19
    @20
    @1
    @27
    @0
    @19
    @20
    @1
    @27
    cB
    @11
    c.x
    cR
    @5
    @6
    c.1
    mulgghm2.b
    mulgghm2.m
    @11
    eqid
    #
    mulgdir
    3exp2
    imp42
    an32s
    @22
    @7
    cz
    wcel
    #
    @8
    @23
    wceq
    @21
    @29
    @2
    @5
    @6
    zaddcl
    adantl
    vn
    @7
    @16
    @23
    cz
    cF
    @15
    @7
    c.1
    c.x
    oveq1
    mulgghm2.f
    @7
    c.1
    c.x
    ovex
    fvmpt
    syl
    @21
    @12
    @26
    wceq
    @2
    @19
    @20
    @9
    @24
    @10
    @25
    @11
    vn
    @5
    @16
    @24
    cz
    cF
    @15
    @5
    c.1
    c.x
    oveq1
    mulgghm2.f
    @5
    c.1
    c.x
    ovex
    fvmpt
    vn
    @6
    @16
    @25
    cz
    cF
    @15
    @6
    c.1
    c.x
    oveq1
    mulgghm2.f
    @6
    c.1
    c.x
    ovex
    fvmpt
    oveqan12d
    adantl
    3eqtr4d
    ralrimivva
    jca
    vy
    vx
    caddc
    @11
    zring
    cR
    cF
    cz
    cB
    zringbas
    mulgghm2.b
    zringplusg
    @28
    isghm
    sylanbrc
end
