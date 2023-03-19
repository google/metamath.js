include "crg.mm"
include "wcel.mm"
include "cmgp.mm"
include "cfv.mm"
include "ccmn.mm"
include "ccrg.mm"
include "isringd.mm"
include "cbs.mm"
include "eqid.mm"
include "mgpbas.mm"
include "syl6eq.mm"
include "cmulr.mm"
include "cplusg.mm"
include "mgpplusg.mm"
include "ismndd.mm"
include "iscmnd.mm"
include "iscrng.mm"
include "sylanbrc.mm"

theorem iscrngd
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
  assume iscrngd.c: |- ( ( ph /\ x e. B /\ y e. B ) -> ( x .x. y ) = ( y .x. x ) )

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
  assert |- ( ph -> R e. CRing )

  proof
    wph
    cR
    crg
    wcel
    cR
    cmgp
    cfv
    #
    ccmn
    wcel
    cR
    ccrg
    wcel
    wph
    vx
    vy
    vz
    cB
    c.pl
    cR
    c.x
    c.1
    isringd.b
    isringd.p
    isringd.t
    isringd.g
    isringd.c
    isringd.a
    isringd.d
    isringd.e
    isringd.u
    isringd.i
    isringd.h
    isringd
    wph
    vx
    vy
    cB
    c.x
    @0
    wph
    cB
    cR
    cbs
    cfv
    #
    @0
    cbs
    cfv
    isringd.b
    @1
    cR
    @0
    @0
    eqid
    #
    @1
    eqid
    mgpbas
    syl6eq
    #
    wph
    c.x
    cR
    cmulr
    cfv
    #
    @0
    cplusg
    cfv
    isringd.t
    cR
    @4
    @0
    @2
    @4
    eqid
    mgpplusg
    syl6eq
    #
    wph
    vx
    vy
    vz
    cB
    c.x
    @0
    c.1
    @3
    @5
    isringd.c
    isringd.a
    isringd.u
    isringd.i
    isringd.h
    ismndd
    iscrngd.c
    iscmnd
    cR
    @0
    @2
    iscrng
    sylanbrc
end
