include "co.mm"
include "wa.mm"
include "cv.mm"
include "wcel.mm"
include "3expb.mm"
include "caovclg.mm"
include "adantlr.mm"
include "caovcld.mm"
include "w3a.mm"
include "wceq.mm"
include "caovassg.mm"
include "caovassd.mm"
include "oveq1d.mm"
include "oveq2.mm"
include "id.mm"
include "eqeq12d.mm"
include "wral.mm"
include "ralrimiva.mm"
include "cbvralv.mm"
include "sylib.mm"
include "adantr.mm"
include "rspcdva.mm"
include "3eqtr3d.mm"
include "oveq2d.mm"
include "eqtrd.mm"
include "grprinvlem.mm"

theorem grprinvd
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cB: class B
  let c.pl: class .+
  let cN: class N
  let cO: class O
  let cX: class X
  let vn: setvar n
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
  assume grprinvlem.c: |- ( ( ph /\ x e. B /\ y e. B ) -> ( x .+ y ) e. B )
  assume grprinvlem.o: |- ( ph -> O e. B )
  assume grprinvlem.i: |- ( ( ph /\ x e. B ) -> ( O .+ x ) = x )
  assume grprinvlem.a: |- ( ( ph /\ ( x e. B /\ y e. B /\ z e. B ) ) -> ( ( x .+ y ) .+ z ) = ( x .+ ( y .+ z ) ) )
  assume grprinvlem.n: |- ( ( ph /\ x e. B ) -> E. y e. B ( y .+ x ) = O )
  assume grprinvd.x: |- ( ( ph /\ ps ) -> X e. B )
  assume grprinvd.n: |- ( ( ph /\ ps ) -> N e. B )
  assume grprinvd.e: |- ( ( ph /\ ps ) -> ( N .+ X ) = O )

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
  disjoint N y
  disjoint N z
  disjoint .+ x
  disjoint .+ y
  disjoint .+ z
  disjoint X y
  disjoint X z
  disjoint ps y
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
  disjoint .+ n
  disjoint .+ u
  disjoint .+ v
  disjoint .+ w
  disjoint X u
  disjoint X v
  disjoint X w
  disjoint ps u
  disjoint ps v
  disjoint ps w
  assert |- ( ( ph /\ ps ) -> ( X .+ N ) = O )

  proof
    wph
    wps
    vx
    vy
    vz
    cB
    c.pl
    cO
    cX
    cN
    c.pl
    co
    #
    grprinvlem.c
    grprinvlem.o
    grprinvlem.i
    grprinvlem.a
    grprinvlem.n
    wph
    wps
    wa
    #
    vu
    vv
    cX
    cN
    cB
    cB
    cB
    c.pl
    wph
    vu
    cv
    #
    cB
    wcel
    #
    vv
    cv
    #
    cB
    wcel
    #
    wa
    @2
    @4
    c.pl
    co
    #
    cB
    wcel
    wps
    wph
    vx
    vy
    @2
    @4
    cB
    cB
    cB
    c.pl
    wph
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
    @7
    @8
    c.pl
    co
    cB
    wcel
    grprinvlem.c
    3expb
    caovclg
    adantlr
    grprinvd.x
    grprinvd.n
    caovcld
    #
    @1
    @0
    @0
    c.pl
    co
    cX
    cN
    @0
    c.pl
    co
    #
    c.pl
    co
    @0
    @1
    vu
    vv
    vw
    cX
    cN
    @0
    cB
    c.pl
    wph
    @3
    @5
    vw
    cv
    #
    cB
    wcel
    w3a
    @6
    @11
    c.pl
    co
    @2
    @4
    @11
    c.pl
    co
    c.pl
    co
    wceq
    wps
    wph
    vx
    vy
    vz
    @2
    @4
    @11
    cB
    c.pl
    grprinvlem.a
    caovassg
    adantlr
    #
    grprinvd.x
    grprinvd.n
    @9
    caovassd
    @1
    @10
    cN
    cX
    c.pl
    @1
    cN
    cX
    c.pl
    co
    #
    cN
    c.pl
    co
    cO
    cN
    c.pl
    co
    #
    @10
    cN
    @1
    @13
    cO
    cN
    c.pl
    grprinvd.e
    oveq1d
    @1
    vu
    vv
    vw
    cN
    cX
    cN
    cB
    c.pl
    @12
    grprinvd.n
    grprinvd.x
    grprinvd.n
    caovassd
    @1
    cO
    @8
    c.pl
    co
    #
    @8
    wceq
    #
    @14
    cN
    wceq
    vy
    cB
    cN
    @8
    cN
    wceq
    #
    @15
    @14
    @8
    cN
    @8
    cN
    cO
    c.pl
    oveq2
    @17
    id
    eqeq12d
    wph
    @16
    vy
    cB
    wral
    #
    wps
    wph
    cO
    @7
    c.pl
    co
    #
    @7
    wceq
    #
    vx
    cB
    wral
    @18
    wph
    @20
    vx
    cB
    grprinvlem.i
    ralrimiva
    @20
    @16
    vx
    vy
    cB
    @7
    @8
    wceq
    #
    @19
    @15
    @7
    @8
    @7
    @8
    cO
    c.pl
    oveq2
    @21
    id
    eqeq12d
    cbvralv
    sylib
    adantr
    grprinvd.n
    rspcdva
    3eqtr3d
    oveq2d
    eqtrd
    grprinvlem
end
