include "tgsss1.mm"

theorem tgsss3
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


  assert |- ( ph -> <" B C A "> ( cgrA ` G ) <" E F D "> )

  proof
    wph
    cB
    cC
    cA
    cE
    cP
    cF
    cD
    cG
    cI
    c.mi
    tgsas.p
    tgsas.m
    tgsas.i
    tgsas.g
    tgsas.b
    tgsas.c
    tgsas.a
    tgsas.e
    tgsas.f
    tgsas.d
    tgsss.2
    tgsss.3
    tgsss.1
    tgsss.5
    tgsss.6
    tgsss.4
    tgsss1
end
