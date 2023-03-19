include "chlg.mm"
include "cfv.mm"
include "eqid.mm"
include "cgrane1.mm"
include "hlid.mm"
include "cgrane2.mm"
include "necomd.mm"
include "tgcgrcomlr.mm"
include "cgracgr.mm"

theorem tgsas1
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
  assume tgsas.p: |- P = ( Base ` G )
  assume tgsas.m: |- .- = ( dist ` G )
  assume tgsas.i: |- I = ( Itv ` G )
  assume tgsas.g: |- ( ph -> G e. TarskiG )
  assume tgsas.a: |- ( ph -> A e. P )
  assume tgsas.b: |- ( ph -> B e. P )
  assume tgsas.c: |- ( ph -> C e. P )
  assume tgsas.d: |- ( ph -> D e. P )
  assume tgsas.e: |- ( ph -> E e. P )
  assume tgsas.f: |- ( ph -> F e. P )
  assume tgsas.1: |- ( ph -> ( A .- B ) = ( D .- E ) )
  assume tgsas.2: |- ( ph -> <" A B C "> ( cgrA ` G ) <" D E F "> )
  assume tgsas.3: |- ( ph -> ( B .- C ) = ( E .- F ) )


  assert |- ( ph -> ( C .- A ) = ( F .- D ) )

  proof
    wph
    cA
    cC
    cD
    cF
    cP
    cG
    cI
    c.mi
    tgsas.p
    tgsas.m
    tgsas.i
    tgsas.g
    tgsas.a
    tgsas.c
    tgsas.d
    tgsas.f
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
    cG
    chlg
    cfv
    #
    c.mi
    cA
    cC
    tgsas.p
    tgsas.i
    @0
    eqid
    #
    tgsas.g
    tgsas.a
    tgsas.b
    tgsas.c
    tgsas.d
    tgsas.e
    tgsas.f
    tgsas.2
    tgsas.a
    tgsas.m
    tgsas.c
    wph
    cA
    cA
    cB
    cP
    cG
    cI
    @0
    tgsas.p
    tgsas.i
    @1
    tgsas.a
    tgsas.a
    tgsas.b
    tgsas.g
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
    tgsas.p
    tgsas.i
    @1
    tgsas.g
    tgsas.a
    tgsas.b
    tgsas.c
    tgsas.d
    tgsas.e
    tgsas.f
    tgsas.2
    cgrane1
    hlid
    wph
    cC
    cA
    cB
    cP
    cG
    cI
    @0
    tgsas.p
    tgsas.i
    @1
    tgsas.c
    tgsas.a
    tgsas.b
    tgsas.g
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
    tgsas.p
    tgsas.i
    @1
    tgsas.g
    tgsas.a
    tgsas.b
    tgsas.c
    tgsas.d
    tgsas.e
    tgsas.f
    tgsas.2
    cgrane2
    necomd
    hlid
    wph
    cA
    cB
    cD
    cE
    cP
    cG
    cI
    c.mi
    tgsas.p
    tgsas.m
    tgsas.i
    tgsas.g
    tgsas.a
    tgsas.b
    tgsas.d
    tgsas.e
    tgsas.1
    tgcgrcomlr
    tgsas.3
    cgracgr
    tgcgrcomlr
end
