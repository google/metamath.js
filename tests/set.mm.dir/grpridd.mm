include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "co.mm"
include "wceq.mm"
include "wrex.mm"
include "oveq1.mm"
include "eqeq1d.mm"
include "cbvrexv.mm"
include "sylib.mm"
include "w3a.mm"
include "caovassg.mm"
include "adantlr.mm"
include "simprl.mm"
include "simprrl.mm"
include "caovassd.mm"
include "simprrr.mm"
include "grprinvd.mm"
include "oveq1d.mm"
include "oveq2d.mm"
include "3eqtr3d.mm"
include "anassrs.mm"
include "rexlimddv.mm"
include "eqtr3d.mm"

theorem grpridd
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cB: class B
  let c.pl: class .+
  let cO: class O
  let vn: setvar n
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
  let cN: class N
  let cX: class X
  let wps: wff ps
  assume grprinvlem.c: |- ( ( ph /\ x e. B /\ y e. B ) -> ( x .+ y ) e. B )
  assume grprinvlem.o: |- ( ph -> O e. B )
  assume grprinvlem.i: |- ( ( ph /\ x e. B ) -> ( O .+ x ) = x )
  assume grprinvlem.a: |- ( ( ph /\ ( x e. B /\ y e. B /\ z e. B ) ) -> ( ( x .+ y ) .+ z ) = ( x .+ ( y .+ z ) ) )
  assume grprinvlem.n: |- ( ( ph /\ x e. B ) -> E. y e. B ( y .+ x ) = O )

  disjoint x y
  disjoint x z
  disjoint B x
  disjoint y z
  disjoint B y
  disjoint B z
  disjoint O x
  disjoint O y
  disjoint O z
  disjoint ph x
  disjoint ph y
  disjoint ph z
  disjoint .+ x
  disjoint .+ y
  disjoint .+ z
  disjoint n u
  disjoint n v
  disjoint n w
  disjoint n x
  disjoint n y
  disjoint n z
  disjoint B n
  disjoint u v
  disjoint u w
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint B u
  disjoint v w
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint B v
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint B w
  disjoint O n
  disjoint O u
  disjoint O v
  disjoint O w
  disjoint n ph
  disjoint ph u
  disjoint ph v
  disjoint ph w
  disjoint N u
  disjoint N v
  disjoint N w
  disjoint N y
  disjoint N z
  disjoint .+ n
  disjoint .+ u
  disjoint .+ v
  disjoint .+ w
  disjoint X u
  disjoint X v
  disjoint X w
  disjoint X y
  disjoint X z
  disjoint ps u
  disjoint ps v
  disjoint ps w
  disjoint ps y
  assert |- ( ( ph /\ x e. B ) -> ( x .+ O ) = x )

  proof
    wph
    vx
    cv
    #
    cB
    wcel
    #
    wa
    #
    cO
    @0
    c.pl
    co
    #
    @0
    cO
    c.pl
    co
    #
    @0
    @2
    vn
    cv
    #
    @0
    c.pl
    co
    #
    cO
    wceq
    #
    @3
    @4
    wceq
    #
    vn
    cB
    @2
    vy
    cv
    #
    @0
    c.pl
    co
    #
    cO
    wceq
    #
    vy
    cB
    wrex
    @7
    vn
    cB
    wrex
    grprinvlem.n
    @11
    @7
    vy
    vn
    cB
    @9
    @5
    wceq
    @10
    @6
    cO
    @9
    @5
    @0
    c.pl
    oveq1
    eqeq1d
    cbvrexv
    sylib
    wph
    @1
    @5
    cB
    wcel
    #
    @7
    wa
    #
    @8
    wph
    @1
    @13
    wa
    #
    wa
    #
    @0
    @5
    c.pl
    co
    #
    @0
    c.pl
    co
    @0
    @6
    c.pl
    co
    @3
    @4
    @15
    vu
    vv
    vw
    @0
    @5
    @0
    cB
    c.pl
    wph
    vu
    cv
    #
    cB
    wcel
    vv
    cv
    #
    cB
    wcel
    vw
    cv
    #
    cB
    wcel
    w3a
    @17
    @18
    c.pl
    co
    @19
    c.pl
    co
    @17
    @18
    @19
    c.pl
    co
    c.pl
    co
    wceq
    @14
    wph
    vx
    vy
    vz
    @17
    @18
    @19
    cB
    c.pl
    grprinvlem.a
    caovassg
    adantlr
    wph
    @1
    @13
    simprl
    #
    wph
    @1
    @12
    @7
    simprrl
    #
    @20
    caovassd
    @15
    @16
    cO
    @0
    c.pl
    wph
    @14
    vx
    vy
    vz
    cB
    c.pl
    @5
    cO
    @0
    grprinvlem.c
    grprinvlem.o
    grprinvlem.i
    grprinvlem.a
    grprinvlem.n
    @20
    @21
    wph
    @1
    @12
    @7
    simprrr
    #
    grprinvd
    oveq1d
    @15
    @6
    cO
    @0
    c.pl
    @22
    oveq2d
    3eqtr3d
    anassrs
    rexlimddv
    grprinvlem.i
    eqtr3d
end
