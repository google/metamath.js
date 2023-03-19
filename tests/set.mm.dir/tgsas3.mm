include "chlg.mm"
include "cfv.mm"
include "eqid.mm"
include "ccgrg.mm"
include "tgsas.mm"
include "cgr3rotl.mm"
include "cgrane4.mm"
include "hlid.mm"
include "cgr3simp2.mm"
include "tgcgrcomlr.mm"
include "tgcgrneq.mm"
include "iscgrad.mm"

theorem tgsas3
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
  assume tgsas2.4: |- ( ph -> A =/= C )


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
    cG
    chlg
    cfv
    #
    cE
    cD
    tgsas.p
    tgsas.i
    @0
    eqid
    #
    tgsas.g
    tgsas.b
    tgsas.c
    tgsas.a
    tgsas.e
    tgsas.f
    tgsas.d
    tgsas.e
    tgsas.d
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
    cI
    c.mi
    tgsas.p
    tgsas.m
    tgsas.i
    @2
    eqid
    #
    tgsas.g
    tgsas.a
    tgsas.b
    tgsas.c
    tgsas.d
    tgsas.e
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
    tgsas
    cgr3rotl
    #
    wph
    cE
    cA
    cF
    cP
    cG
    cI
    @0
    tgsas.p
    tgsas.i
    @1
    tgsas.e
    tgsas.a
    tgsas.f
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
    cgrane4
    hlid
    wph
    cD
    cA
    cF
    cP
    cG
    cI
    @0
    tgsas.p
    tgsas.i
    @1
    tgsas.d
    tgsas.a
    tgsas.f
    tgsas.g
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
    cC
    cA
    cF
    cD
    cP
    cG
    cI
    c.mi
    tgsas.p
    tgsas.m
    tgsas.i
    tgsas.g
    tgsas.c
    tgsas.a
    tgsas.f
    tgsas.d
    wph
    cB
    cC
    cA
    cE
    cP
    @2
    cF
    cD
    cG
    cI
    c.mi
    tgsas.p
    tgsas.m
    tgsas.i
    @3
    tgsas.g
    tgsas.b
    tgsas.c
    tgsas.a
    tgsas.e
    tgsas.f
    tgsas.d
    @4
    cgr3simp2
    tgcgrcomlr
    tgsas2.4
    tgcgrneq
    hlid
    iscgrad
end
