include "cgrp.mm"
include "wcel.mm"
include "cmgp.mm"
include "cfv.mm"
include "cmnd.mm"
include "cv.mm"
include "cplusg.mm"
include "co.mm"
include "cmulr.mm"
include "wceq.mm"
include "wa.mm"
include "cbs.mm"
include "wral.mm"
include "crg.mm"
include "eqid.mm"
include "mgpbas.mm"
include "syl6eq.mm"
include "mgpplusg.mm"
include "ismndd.mm"
include "w3a.mm"
include "eleq2d.mm"
include "3anbi123d.mm"
include "biimpar.mm"
include "adantr.mm"
include "eqidd.mm"
include "oveqdr.mm"
include "oveq123d.mm"
include "3eqtr3d.mm"
include "jca.mm"
include "syldan.mm"
include "ralrimivvva.mm"
include "isring.mm"
include "syl3anbrc.mm"

theorem isringd
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cB: class B
  let c.pl: class .+
  let cR: class R
  let c.x: class .x.
  let c.1: class .1.
  assume isringd.b: |- ( ph -> B = ( Base ` R ) )
  assume isringd.p: |- ( ph -> .+ = ( +g ` R ) )
  assume isringd.t: |- ( ph -> .x. = ( .r ` R ) )
  assume isringd.g: |- ( ph -> R e. Grp )
  assume isringd.c: |- ( ( ph /\ x e. B /\ y e. B ) -> ( x .x. y ) e. B )
  assume isringd.a: |- ( ( ph /\ ( x e. B /\ y e. B /\ z e. B ) ) -> ( ( x .x. y ) .x. z ) = ( x .x. ( y .x. z ) ) )
  assume isringd.d: |- ( ( ph /\ ( x e. B /\ y e. B /\ z e. B ) ) -> ( x .x. ( y .+ z ) ) = ( ( x .x. y ) .+ ( x .x. z ) ) )
  assume isringd.e: |- ( ( ph /\ ( x e. B /\ y e. B /\ z e. B ) ) -> ( ( x .+ y ) .x. z ) = ( ( x .x. z ) .+ ( y .x. z ) ) )
  assume isringd.u: |- ( ph -> .1. e. B )
  assume isringd.i: |- ( ( ph /\ x e. B ) -> ( .1. .x. x ) = x )
  assume isringd.h: |- ( ( ph /\ x e. B ) -> ( x .x. .1. ) = x )

  disjoint .1. x
  disjoint x y
  disjoint x z
  disjoint B x
  disjoint y z
  disjoint B y
  disjoint B z
  disjoint ph x
  disjoint ph y
  disjoint ph z
  disjoint R x
  disjoint R y
  disjoint R z
  assert |- ( ph -> R e. Ring )

  proof
    wph
    cR
    cgrp
    wcel
    cR
    cmgp
    cfv
    #
    cmnd
    wcel
    vx
    cv
    #
    vy
    cv
    #
    vz
    cv
    #
    cR
    cplusg
    cfv
    #
    co
    #
    cR
    cmulr
    cfv
    #
    co
    #
    @1
    @2
    @6
    co
    #
    @1
    @3
    @6
    co
    #
    @4
    co
    #
    wceq
    #
    @1
    @2
    @4
    co
    #
    @3
    @6
    co
    #
    @9
    @2
    @3
    @6
    co
    #
    @4
    co
    #
    wceq
    #
    wa
    #
    vz
    cR
    cbs
    cfv
    #
    wral
    vy
    @18
    wral
    vx
    @18
    wral
    cR
    crg
    wcel
    isringd.g
    wph
    vx
    vy
    vz
    cB
    c.x
    @0
    c.1
    wph
    cB
    @18
    @0
    cbs
    cfv
    isringd.b
    @18
    cR
    @0
    @0
    eqid
    #
    @18
    eqid
    #
    mgpbas
    syl6eq
    wph
    c.x
    @6
    @0
    cplusg
    cfv
    isringd.t
    cR
    @6
    @0
    @19
    @6
    eqid
    #
    mgpplusg
    syl6eq
    isringd.c
    isringd.a
    isringd.u
    isringd.i
    isringd.h
    ismndd
    wph
    @17
    vx
    vy
    vz
    @18
    @18
    @18
    wph
    @1
    @18
    wcel
    #
    @2
    @18
    wcel
    #
    @3
    @18
    wcel
    #
    w3a
    #
    @1
    cB
    wcel
    #
    @2
    cB
    wcel
    #
    @3
    cB
    wcel
    #
    w3a
    #
    @17
    wph
    @29
    @25
    wph
    @26
    @22
    @27
    @23
    @28
    @24
    wph
    cB
    @18
    @1
    isringd.b
    eleq2d
    wph
    cB
    @18
    @2
    isringd.b
    eleq2d
    wph
    cB
    @18
    @3
    isringd.b
    eleq2d
    3anbi123d
    biimpar
    wph
    @29
    wa
    #
    @11
    @16
    @30
    @1
    @2
    @3
    c.pl
    co
    #
    c.x
    co
    @1
    @2
    c.x
    co
    #
    @1
    @3
    c.x
    co
    #
    c.pl
    co
    @7
    @10
    isringd.d
    @30
    @1
    @1
    @31
    @5
    c.x
    @6
    wph
    c.x
    @6
    wceq
    @29
    isringd.t
    adantr
    #
    @30
    @1
    eqidd
    wph
    @29
    vy
    vz
    c.pl
    @4
    isringd.p
    oveqdr
    oveq123d
    @30
    @32
    @8
    @33
    @9
    c.pl
    @4
    wph
    c.pl
    @4
    wceq
    @29
    isringd.p
    adantr
    #
    wph
    @29
    vx
    vy
    c.x
    @6
    isringd.t
    oveqdr
    wph
    @29
    vx
    vz
    c.x
    @6
    isringd.t
    oveqdr
    #
    oveq123d
    3eqtr3d
    @30
    @1
    @2
    c.pl
    co
    #
    @3
    c.x
    co
    @33
    @2
    @3
    c.x
    co
    #
    c.pl
    co
    @13
    @15
    isringd.e
    @30
    @37
    @12
    @3
    @3
    c.x
    @6
    @34
    wph
    @29
    vx
    vy
    c.pl
    @4
    isringd.p
    oveqdr
    @30
    @3
    eqidd
    oveq123d
    @30
    @33
    @9
    @38
    @14
    c.pl
    @4
    @35
    @36
    wph
    @29
    vy
    vz
    c.x
    @6
    isringd.t
    oveqdr
    oveq123d
    3eqtr3d
    jca
    syldan
    ralrimivvva
    vx
    vy
    vz
    @18
    @4
    cR
    @6
    @0
    @20
    @19
    @4
    eqid
    @21
    isring
    syl3anbrc
end
