include "ccgrg.mm"
include "cfv.mm"
include "eqid.mm"
include "tgsas1.mm"
include "trgcgr.mm"

theorem tgsas
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


  assert |- ( ph -> <" A B C "> ( cgrG ` G ) <" D E F "> )

  proof
    wph
    cA
    cB
    cC
    cD
    cP
    cG
    ccgrg
    cfv
    #
    cE
    cF
    cG
    c.mi
    tgsas.p
    tgsas.m
    @0
    eqid
    tgsas.g
    tgsas.a
    tgsas.b
    tgsas.c
    tgsas.d
    tgsas.e
    tgsas.f
    tgsas.1
    tgsas.3
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
    c.mi
    tgsas.p
    tgsas.m
    tgsas.i
    tgsas.g
    tgsas.a
    tgsas.b
    tgsas.c
    tgsas.d
    tgsas.e
    tgsas.f
    tgsas.1
    tgsas.2
    tgsas.3
    tgsas1
    trgcgr
end
