include "cmgm.mm"
include "wcel.mm"
include "cv.mm"
include "cmpt2.mm"
include "co.mm"
include "wceq.mm"
include "wral.mm"
include "csgrp.mm"
include "wa.mm"
include "adantr.mm"
include "opmpt2ismgm.mm"
include "w3a.mm"
include "eqidd.mm"
include "weq.mm"
include "simpl.mm"
include "simpr3.mm"
include "ovmpt2d.mm"
include "simpr1.mm"
include "eqtr4d.mm"
include "sylan.mm"
include "simpr2.mm"
include "oveq1d.mm"
include "oveq2d.mm"
include "3eqtr4d.mm"
include "ralrimivvva.mm"
include "cplusg.mm"
include "cfv.mm"
include "eqcomi.mm"
include "issgrp.mm"
include "sylanbrc.mm"

theorem copissgrp
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cB: class B
  let cC: class C
  let cM: class M
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vk: setvar k
  assume copissgrp.b: |- B = ( Base ` M )
  assume copissgrp.p: |- ( +g ` M ) = ( x e. B , y e. B |-> C )
  assume copissgrp.n: |- ( ph -> B =/= (/) )
  assume copissgrp.c: |- ( ph -> C e. B )

  disjoint B x
  disjoint B y
  disjoint x y
  disjoint C x
  disjoint C y
  disjoint M x
  disjoint ph x
  disjoint ph y
  disjoint B a
  disjoint B b
  disjoint B c
  disjoint a b
  disjoint a c
  disjoint a x
  disjoint a y
  disjoint b c
  disjoint b x
  disjoint b y
  disjoint c x
  disjoint c y
  disjoint C a
  disjoint C b
  disjoint C c
  disjoint M a
  disjoint M b
  disjoint M c
  disjoint a ph
  disjoint b ph
  disjoint c ph
  disjoint k x
  assert |- ( ph -> M e. SGrp )

  proof
    wph
    cM
    cmgm
    wcel
    va
    cv
    #
    vb
    cv
    #
    vx
    vy
    cB
    cB
    cC
    cmpt2
    #
    co
    #
    vc
    cv
    #
    @2
    co
    #
    @0
    @1
    @4
    @2
    co
    #
    @2
    co
    #
    wceq
    #
    vc
    cB
    wral
    vb
    cB
    wral
    va
    cB
    wral
    cM
    csgrp
    wcel
    wph
    vx
    vy
    cB
    cC
    cM
    copissgrp.b
    copissgrp.p
    copissgrp.n
    wph
    cC
    cB
    wcel
    #
    vx
    cv
    #
    cB
    wcel
    vy
    cv
    #
    cB
    wcel
    wa
    copissgrp.c
    adantr
    opmpt2ismgm
    wph
    @8
    va
    vb
    vc
    cB
    cB
    cB
    wph
    @0
    cB
    wcel
    #
    @1
    cB
    wcel
    #
    @4
    cB
    wcel
    #
    w3a
    #
    wa
    #
    cC
    @4
    @2
    co
    #
    @0
    cC
    @2
    co
    #
    @5
    @7
    wph
    @9
    @15
    @17
    @18
    wceq
    copissgrp.c
    @9
    @15
    wa
    #
    @17
    cC
    @18
    @19
    vx
    vy
    cC
    @4
    cB
    cB
    cC
    cC
    @2
    cB
    @19
    @2
    eqidd
    #
    @19
    @10
    cC
    wceq
    vy
    vc
    weq
    #
    wa
    wa
    cC
    eqidd
    @9
    @15
    simpl
    #
    @9
    @12
    @13
    @14
    simpr3
    @22
    ovmpt2d
    @19
    vx
    vy
    @0
    cC
    cB
    cB
    cC
    cC
    @2
    cB
    @20
    @19
    vx
    va
    weq
    #
    @11
    cC
    wceq
    wa
    wa
    cC
    eqidd
    @9
    @12
    @13
    @14
    simpr1
    @22
    @22
    ovmpt2d
    eqtr4d
    sylan
    @16
    @3
    cC
    @4
    @2
    @16
    vx
    vy
    @0
    @1
    cB
    cB
    cC
    cC
    @2
    cB
    @16
    @2
    eqidd
    #
    @16
    @23
    vy
    vb
    weq
    wa
    wa
    cC
    eqidd
    wph
    @12
    @13
    @14
    simpr1
    wph
    @12
    @13
    @14
    simpr2
    #
    wph
    @9
    @15
    copissgrp.c
    adantr
    #
    ovmpt2d
    oveq1d
    @16
    @6
    cC
    @0
    @2
    @16
    vx
    vy
    @1
    @4
    cB
    cB
    cC
    cC
    @2
    cB
    @24
    @16
    vx
    vb
    weq
    @21
    wa
    wa
    cC
    eqidd
    @25
    wph
    @12
    @13
    @14
    simpr3
    @26
    ovmpt2d
    oveq2d
    3eqtr4d
    ralrimivvva
    va
    vb
    vc
    cB
    cM
    @2
    copissgrp.b
    cM
    cplusg
    cfv
    @2
    copissgrp.p
    eqcomi
    issgrp
    sylanbrc
end
