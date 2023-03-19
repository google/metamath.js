include "chlg.mm"
include "cfv.mm"
include "eqid.mm"
include "ccgrg.mm"
include "trgcgr.mm"
include "tgcgrneq.mm"
include "hlid.mm"
include "necomd.mm"
include "iscgrad.mm"

theorem tgsss1
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


  assert |- ( ph -> <" A B C "> ( cgrA ` G ) <" D E F "> )

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
    cG
    chlg
    cfv
    #
    cD
    cF
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
    tgsas.d
    tgsas.f
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
    @2
    eqid
    tgsas.g
    tgsas.a
    tgsas.b
    tgsas.c
    tgsas.d
    tgsas.e
    tgsas.f
    tgsss.1
    tgsss.2
    tgsss.3
    trgcgr
    wph
    cD
    cA
    cE
    cP
    cG
    cI
    @0
    tgsas.p
    tgsas.i
    @1
    tgsas.d
    tgsas.a
    tgsas.e
    tgsas.g
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
    tgsss.1
    tgsss.4
    tgcgrneq
    hlid
    wph
    cF
    cA
    cE
    cP
    cG
    cI
    @0
    tgsas.p
    tgsas.i
    @1
    tgsas.f
    tgsas.a
    tgsas.e
    tgsas.g
    wph
    cE
    cF
    wph
    cB
    cC
    cE
    cF
    cP
    cG
    cI
    c.mi
    tgsas.p
    tgsas.m
    tgsas.i
    tgsas.g
    tgsas.b
    tgsas.c
    tgsas.e
    tgsas.f
    tgsss.2
    tgsss.5
    tgcgrneq
    necomd
    hlid
    iscgrad
end
