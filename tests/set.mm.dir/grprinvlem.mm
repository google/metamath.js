include "wa.mm"
include "cv.mm"
include "co.mm"
include "wceq.mm"
include "wrex.mm"
include "wral.mm"
include "wcel.mm"
include "ralrimiva.mm"
include "oveq2.mm"
include "eqeq1d.mm"
include "rexbidv.mm"
include "cbvralv.mm"
include "sylib.mm"
include "rspccva.mm"
include "syl2an2r.mm"
include "oveq2d.mm"
include "adantr.mm"
include "simprr.mm"
include "oveq1d.mm"
include "w3a.mm"
include "caovassg.mm"
include "ad4ant14.mm"
include "simprl.mm"
include "caovassd.mm"
include "id.mm"
include "eqeq12d.mm"
include "rspcdva.mm"
include "3eqtr3d.mm"
include "rexlimddv.mm"

theorem grprinvlem
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cB: class B
  let c.pl: class .+
  let cO: class O
  let cX: class X
  let vn: setvar n
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
  let cN: class N
  assume grprinvlem.c: |- ( ( ph /\ x e. B /\ y e. B ) -> ( x .+ y ) e. B )
  assume grprinvlem.o: |- ( ph -> O e. B )
  assume grprinvlem.i: |- ( ( ph /\ x e. B ) -> ( O .+ x ) = x )
  assume grprinvlem.a: |- ( ( ph /\ ( x e. B /\ y e. B /\ z e. B ) ) -> ( ( x .+ y ) .+ z ) = ( x .+ ( y .+ z ) ) )
  assume grprinvlem.n: |- ( ( ph /\ x e. B ) -> E. y e. B ( y .+ x ) = O )
  assume grprinvlem.x: |- ( ( ph /\ ps ) -> X e. B )
  assume grprinvlem.e: |- ( ( ph /\ ps ) -> ( X .+ X ) = X )

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
  disjoint N y
  disjoint N z
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
  assert |- ( ( ph /\ ps ) -> X = O )

  proof
    wph
    wps
    wa
    #
    vy
    cv
    #
    cX
    c.pl
    co
    #
    cO
    wceq
    #
    cX
    cO
    wceq
    vy
    cB
    wph
    @1
    vz
    cv
    #
    c.pl
    co
    #
    cO
    wceq
    #
    vy
    cB
    wrex
    #
    vz
    cB
    wral
    #
    wps
    cX
    cB
    wcel
    #
    @3
    vy
    cB
    wrex
    #
    wph
    @1
    vx
    cv
    #
    c.pl
    co
    #
    cO
    wceq
    #
    vy
    cB
    wrex
    #
    vx
    cB
    wral
    @8
    wph
    @14
    vx
    cB
    grprinvlem.n
    ralrimiva
    @14
    @7
    vx
    vz
    cB
    @11
    @4
    wceq
    #
    @13
    @6
    vy
    cB
    @15
    @12
    @5
    cO
    @11
    @4
    @1
    c.pl
    oveq2
    eqeq1d
    rexbidv
    cbvralv
    sylib
    grprinvlem.x
    @7
    @10
    vz
    cX
    cB
    @4
    cX
    wceq
    #
    @6
    @3
    vy
    cB
    @16
    @5
    @2
    cO
    @4
    cX
    @1
    c.pl
    oveq2
    eqeq1d
    rexbidv
    rspccva
    syl2an2r
    @0
    @1
    cB
    wcel
    #
    @3
    wa
    #
    wa
    #
    @1
    cX
    cX
    c.pl
    co
    #
    c.pl
    co
    #
    @2
    cX
    cO
    @0
    @21
    @2
    wceq
    @18
    @0
    @20
    cX
    @1
    c.pl
    grprinvlem.e
    oveq2d
    adantr
    @19
    @2
    cX
    c.pl
    co
    cO
    cX
    c.pl
    co
    #
    @21
    cX
    @19
    @2
    cO
    cX
    c.pl
    @0
    @17
    @3
    simprr
    #
    oveq1d
    @19
    vu
    vv
    vw
    @1
    cX
    cX
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
    @24
    @25
    c.pl
    co
    @26
    c.pl
    co
    @24
    @25
    @26
    c.pl
    co
    c.pl
    co
    wceq
    wps
    @18
    wph
    vx
    vy
    vz
    @24
    @25
    @26
    cB
    c.pl
    grprinvlem.a
    caovassg
    ad4ant14
    @0
    @17
    @3
    simprl
    @0
    @9
    @18
    grprinvlem.x
    adantr
    #
    @27
    caovassd
    @0
    @22
    cX
    wceq
    #
    @18
    @0
    cO
    @1
    c.pl
    co
    #
    @1
    wceq
    #
    @28
    vy
    cB
    cX
    @1
    cX
    wceq
    #
    @29
    @22
    @1
    cX
    @1
    cX
    cO
    c.pl
    oveq2
    @31
    id
    eqeq12d
    wph
    @30
    vy
    cB
    wral
    #
    wps
    wph
    cO
    @11
    c.pl
    co
    #
    @11
    wceq
    #
    vx
    cB
    wral
    @32
    wph
    @34
    vx
    cB
    grprinvlem.i
    ralrimiva
    @34
    @30
    vx
    vy
    cB
    @11
    @1
    wceq
    #
    @33
    @29
    @11
    @1
    @11
    @1
    cO
    c.pl
    oveq2
    @35
    id
    eqeq12d
    cbvralv
    sylib
    adantr
    grprinvlem.x
    rspcdva
    adantr
    3eqtr3d
    @23
    3eqtr3d
    rexlimddv
end
