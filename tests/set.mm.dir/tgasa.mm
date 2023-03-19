include "tgasa1.mm"
include "tgsas.mm"

theorem tgasa
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
  let cL: class L
  let c.mi: class .-
  let va: setvar a
  let vb: setvar b
  let vf: setvar f
  let vw: setvar w
  let vt: setvar t
  let vu: setvar u
  let vv: setvar v
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
  assume tgasa.l: |- L = ( LineG ` G )
  assume tgasa.1: |- ( ph -> -. ( C e. ( A L B ) \/ A = B ) )
  assume tgasa.2: |- ( ph -> ( A .- B ) = ( D .- E ) )
  assume tgasa.3: |- ( ph -> <" A B C "> ( cgrA ` G ) <" D E F "> )
  assume tgasa.4: |- ( ph -> <" C A B "> ( cgrA ` G ) <" F D E "> )


  assert |- ( ph -> <" A B C "> ( cgrG ` G ) <" D E F "> )

  proof
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
    tgasa.2
    tgasa.3
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
    cL
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
    tgasa.l
    tgasa.1
    tgasa.2
    tgasa.3
    tgasa.4
    tgasa1
    tgsas
end
