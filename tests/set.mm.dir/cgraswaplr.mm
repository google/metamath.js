include "chlg.mm"
include "cfv.mm"
include "eqid.mm"
include "cgrane2.mm"
include "necomd.mm"
include "cgrane1.mm"
include "cgraswap.mm"
include "cgratr.mm"
include "cgrane3.mm"
include "cgrane4.mm"

theorem cgraswaplr
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cP: class P
  let cE: class E
  let cF: class F
  let cG: class G
  let cI: class I
  let c.mi: class .-
  let vx: setvar x
  let vy: setvar y
  assume cgracol.p: |- P = ( Base ` G )
  assume cgracol.i: |- I = ( Itv ` G )
  assume cgracol.m: |- .- = ( dist ` G )
  assume cgracol.g: |- ( ph -> G e. TarskiG )
  assume cgracol.a: |- ( ph -> A e. P )
  assume cgracol.b: |- ( ph -> B e. P )
  assume cgracol.c: |- ( ph -> C e. P )
  assume cgracol.d: |- ( ph -> D e. P )
  assume cgracol.e: |- ( ph -> E e. P )
  assume cgracol.f: |- ( ph -> F e. P )
  assume cgracol.1: |- ( ph -> <" A B C "> ( cgrA ` G ) <" D E F "> )


  assert |- ( ph -> <" C B A "> ( cgrA ` G ) <" F E D "> )

  proof
    wph
    cC
    cB
    cA
    cD
    cP
    cE
    cE
    cF
    cG
    cF
    cI
    cD
    cG
    chlg
    cfv
    #
    cgracol.p
    cgracol.i
    cgracol.g
    @0
    eqid
    #
    cgracol.c
    cgracol.b
    cgracol.a
    cgracol.d
    cgracol.e
    cgracol.f
    wph
    cC
    cB
    cA
    cA
    cP
    cE
    cB
    cC
    cG
    cD
    cI
    cF
    @0
    cgracol.p
    cgracol.i
    cgracol.g
    @1
    cgracol.c
    cgracol.b
    cgracol.a
    cgracol.a
    cgracol.b
    cgracol.c
    wph
    cC
    cB
    cA
    cP
    cG
    cI
    @0
    cgracol.p
    cgracol.i
    cgracol.g
    @1
    cgracol.c
    cgracol.b
    cgracol.a
    wph
    cB
    cC
    wph
    cA
    cB
    cC
    cD
    cP
    cE
    cF
    cG
    cI
    @0
    cgracol.p
    cgracol.i
    @1
    cgracol.g
    cgracol.a
    cgracol.b
    cgracol.c
    cgracol.d
    cgracol.e
    cgracol.f
    cgracol.1
    cgrane2
    necomd
    wph
    cA
    cB
    wph
    cA
    cB
    cC
    cD
    cP
    cE
    cF
    cG
    cI
    @0
    cgracol.p
    cgracol.i
    @1
    cgracol.g
    cgracol.a
    cgracol.b
    cgracol.c
    cgracol.d
    cgracol.e
    cgracol.f
    cgracol.1
    cgrane1
    necomd
    cgraswap
    cgracol.d
    cgracol.e
    cgracol.f
    cgracol.1
    cgratr
    cgracol.f
    cgracol.e
    cgracol.d
    wph
    cD
    cE
    cF
    cP
    cG
    cI
    @0
    cgracol.p
    cgracol.i
    cgracol.g
    @1
    cgracol.d
    cgracol.e
    cgracol.f
    wph
    cE
    cD
    wph
    cA
    cB
    cC
    cD
    cP
    cE
    cF
    cG
    cI
    @0
    cgracol.p
    cgracol.i
    @1
    cgracol.g
    cgracol.a
    cgracol.b
    cgracol.c
    cgracol.d
    cgracol.e
    cgracol.f
    cgracol.1
    cgrane3
    necomd
    wph
    cA
    cB
    cC
    cD
    cP
    cE
    cF
    cG
    cI
    @0
    cgracol.p
    cgracol.i
    @1
    cgracol.g
    cgracol.a
    cgracol.b
    cgracol.c
    cgracol.d
    cgracol.e
    cgracol.f
    cgracol.1
    cgrane4
    cgraswap
    cgratr
end
