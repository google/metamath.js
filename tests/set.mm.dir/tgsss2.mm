include "tgsss1.mm"

theorem tgsss2
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
  assume tgsss.1: |- ( ph -> ( A .- B ) = ( D .- E ) )
  assume tgsss.2: |- ( ph -> ( B .- C ) = ( E .- F ) )
  assume tgsss.3: |- ( ph -> ( C .- A ) = ( F .- D ) )
  assume tgsss.4: |- ( ph -> A =/= B )
  assume tgsss.5: |- ( ph -> B =/= C )
  assume tgsss.6: |- ( ph -> C =/= A )


  assert |- ( ph -> <" C A B "> ( cgrA ` G ) <" F D E "> )

  proof
    wph
    cC
    cA
    cB
    cF
    cP
    cD
    cE
    cG
    cI
    c.mi
    tgsas.p
    tgsas.m
    tgsas.i
    tgsas.g
    tgsas.c
    tgsas.a
    tgsas.b
    tgsas.f
    tgsas.d
    tgsas.e
    tgsss.3
    tgsss.1
    tgsss.2
    tgsss.6
    tgsss.4
    tgsss.5
    tgsss1
end
