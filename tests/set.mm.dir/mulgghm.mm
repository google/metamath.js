include "cabl.mm"
include "wcel.mm"
include "cz.mm"
include "wa.mm"
include "cplusg.mm"
include "cfv.mm"
include "cv.mm"
include "co.mm"
include "cmpt.mm"
include "eqid.mm"
include "cgrp.mm"
include "ablgrp.mm"
include "adantr.mm"
include "mulgcl.mm"
include "syl3an1.mm"
include "3expa.mm"
include "fmptd.mm"
include "wceq.mm"
include "w3a.mm"
include "3anass.mm"
include "mulgdi.mm"
include "sylan2br.mm"
include "anassrs.mm"
include "grpcl.mm"
include "3expb.mm"
include "sylan.mm"
include "oveq2.mm"
include "ovex.mm"
include "fvmpt.mm"
include "syl.mm"
include "oveqan12d.mm"
include "adantl.mm"
include "3eqtr4d.mm"
include "isghmd.mm"

theorem mulgghm
  let vx: setvar x
  let cB: class B
  let c.x: class .x.
  let cG: class G
  let cM: class M
  let vy: setvar y
  let vz: setvar z
  assume mulgmhm.b: |- B = ( Base ` G )
  assume mulgmhm.m: |- .x. = ( .g ` G )

  disjoint B x
  disjoint G x
  disjoint M x
  disjoint .x. x
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint B y
  disjoint B z
  disjoint G y
  disjoint G z
  disjoint M y
  disjoint M z
  disjoint .x. y
  disjoint .x. z
  assert |- ( ( G e. Abel /\ M e. ZZ ) -> ( x e. B |-> ( M .x. x ) ) e. ( G GrpHom G ) )

  proof
    cG
    cabl
    wcel
    #
    cM
    cz
    wcel
    #
    wa
    #
    vy
    vz
    cG
    cplusg
    cfv
    #
    @3
    cG
    cG
    vx
    cB
    cM
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
    mulgmhm.b
    mulgmhm.b
    @3
    eqid
    #
    @7
    @0
    cG
    cgrp
    wcel
    #
    @1
    cG
    ablgrp
    #
    adantr
    #
    @10
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
    #
    @5
    cB
    wcel
    #
    @0
    @8
    @1
    @11
    @12
    @9
    cB
    c.x
    cG
    cM
    @4
    mulgmhm.b
    mulgmhm.m
    mulgcl
    syl3an1
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
    cM
    @14
    @16
    @3
    co
    #
    c.x
    co
    #
    cM
    @14
    c.x
    co
    #
    cM
    @16
    c.x
    co
    #
    @3
    co
    #
    @20
    @6
    cfv
    #
    @14
    @6
    cfv
    #
    @16
    @6
    cfv
    #
    @3
    co
    #
    @0
    @1
    @18
    @21
    @24
    wceq
    #
    @1
    @18
    wa
    @0
    @1
    @15
    @17
    w3a
    @29
    @1
    @15
    @17
    3anass
    cB
    @3
    c.x
    cG
    cM
    @14
    @16
    mulgmhm.b
    mulgmhm.m
    @7
    mulgdi
    sylan2br
    anassrs
    @19
    @20
    cB
    wcel
    #
    @25
    @21
    wceq
    @2
    @8
    @18
    @30
    @10
    @8
    @15
    @17
    @30
    cB
    @3
    cG
    @14
    @16
    mulgmhm.b
    @7
    grpcl
    3expb
    sylan
    vx
    @20
    @5
    @21
    cB
    @6
    @4
    @20
    cM
    c.x
    oveq2
    @13
    cM
    @20
    c.x
    ovex
    fvmpt
    syl
    @18
    @28
    @24
    wceq
    @2
    @15
    @17
    @26
    @22
    @27
    @23
    @3
    vx
    @14
    @5
    @22
    cB
    @6
    @4
    @14
    cM
    c.x
    oveq2
    @13
    cM
    @14
    c.x
    ovex
    fvmpt
    vx
    @16
    @5
    @23
    cB
    @6
    @4
    @16
    cM
    c.x
    oveq2
    @13
    cM
    @16
    c.x
    ovex
    fvmpt
    oveqan12d
    adantl
    3eqtr4d
    isghmd
end
