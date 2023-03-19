include "cfv.mm"
include "cstrkg.mm"
include "motcl.mm"
include "eqeltrd.mm"
include "co.mm"
include "oveq12d.mm"
include "motcgr.mm"
include "eqtr2d.mm"
include "trgcgr.mm"

theorem motcgr3
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cP: class P
  let c.sm: class .~
  let cE: class E
  let cF: class F
  let cG: class G
  let cH: class H
  let c.mi: class .-
  assume motcgr3.p: |- P = ( Base ` G )
  assume motcgr3.m: |- .- = ( dist ` G )
  assume motcgr3.r: |- .~ = ( cgrG ` G )
  assume motcgr3.g: |- ( ph -> G e. TarskiG )
  assume motcgr3.a: |- ( ph -> A e. P )
  assume motcgr3.b: |- ( ph -> B e. P )
  assume motcgr3.c: |- ( ph -> C e. P )
  assume motcgr3.d: |- ( ph -> D = ( H ` A ) )
  assume motcgr3.e: |- ( ph -> E = ( H ` B ) )
  assume motcgr3.f: |- ( ph -> F = ( H ` C ) )
  assume motcgr3.h: |- ( ph -> H e. ( G Ismt G ) )


  assert |- ( ph -> <" A B C "> .~ <" D E F "> )

  proof
    wph
    cA
    cB
    cC
    cD
    cP
    c.sm
    cE
    cF
    cG
    c.mi
    motcgr3.p
    motcgr3.m
    motcgr3.r
    motcgr3.g
    motcgr3.a
    motcgr3.b
    motcgr3.c
    wph
    cD
    cA
    cH
    cfv
    #
    cP
    motcgr3.d
    wph
    cA
    cP
    cH
    cG
    c.mi
    cstrkg
    motcgr3.p
    motcgr3.m
    motcgr3.g
    motcgr3.h
    motcgr3.a
    motcl
    eqeltrd
    wph
    cE
    cB
    cH
    cfv
    #
    cP
    motcgr3.e
    wph
    cB
    cP
    cH
    cG
    c.mi
    cstrkg
    motcgr3.p
    motcgr3.m
    motcgr3.g
    motcgr3.h
    motcgr3.b
    motcl
    eqeltrd
    wph
    cF
    cC
    cH
    cfv
    #
    cP
    motcgr3.f
    wph
    cC
    cP
    cH
    cG
    c.mi
    cstrkg
    motcgr3.p
    motcgr3.m
    motcgr3.g
    motcgr3.h
    motcgr3.c
    motcl
    eqeltrd
    wph
    cD
    cE
    c.mi
    co
    @0
    @1
    c.mi
    co
    cA
    cB
    c.mi
    co
    wph
    cD
    @0
    cE
    @1
    c.mi
    motcgr3.d
    motcgr3.e
    oveq12d
    wph
    cA
    cB
    cP
    cH
    cG
    c.mi
    cstrkg
    motcgr3.p
    motcgr3.m
    motcgr3.g
    motcgr3.a
    motcgr3.b
    motcgr3.h
    motcgr
    eqtr2d
    wph
    cE
    cF
    c.mi
    co
    @1
    @2
    c.mi
    co
    cB
    cC
    c.mi
    co
    wph
    cE
    @1
    cF
    @2
    c.mi
    motcgr3.e
    motcgr3.f
    oveq12d
    wph
    cB
    cC
    cP
    cH
    cG
    c.mi
    cstrkg
    motcgr3.p
    motcgr3.m
    motcgr3.g
    motcgr3.b
    motcgr3.c
    motcgr3.h
    motcgr
    eqtr2d
    wph
    cF
    cD
    c.mi
    co
    @2
    @0
    c.mi
    co
    cC
    cA
    c.mi
    co
    wph
    cF
    @2
    cD
    @0
    c.mi
    motcgr3.f
    motcgr3.d
    oveq12d
    wph
    cC
    cA
    cP
    cH
    cG
    c.mi
    cstrkg
    motcgr3.p
    motcgr3.m
    motcgr3.g
    motcgr3.c
    motcgr3.a
    motcgr3.h
    motcgr
    eqtr2d
    trgcgr
end
