include "co.mm"
include "eqidd.mm"
include "eqtr4d.mm"
include "tgcgrextend.mm"
include "axtg5seg.mm"
include "eqcomd.mm"
include "axtgcgrid.mm"

theorem tgsegconeq
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
  assume tkgeom.p: |- P = ( Base ` G )
  assume tkgeom.d: |- .- = ( dist ` G )
  assume tkgeom.i: |- I = ( Itv ` G )
  assume tkgeom.g: |- ( ph -> G e. TarskiG )
  assume tgcgrextend.a: |- ( ph -> A e. P )
  assume tgcgrextend.b: |- ( ph -> B e. P )
  assume tgcgrextend.c: |- ( ph -> C e. P )
  assume tgcgrextend.d: |- ( ph -> D e. P )
  assume tgcgrextend.e: |- ( ph -> E e. P )
  assume tgcgrextend.f: |- ( ph -> F e. P )
  assume tgsegconeq.1: |- ( ph -> D =/= A )
  assume tgsegconeq.2: |- ( ph -> A e. ( D I E ) )
  assume tgsegconeq.3: |- ( ph -> A e. ( D I F ) )
  assume tgsegconeq.4: |- ( ph -> ( A .- E ) = ( B .- C ) )
  assume tgsegconeq.5: |- ( ph -> ( A .- F ) = ( B .- C ) )


  assert |- ( ph -> E = F )

  proof
    wph
    cP
    cG
    cI
    c.mi
    cE
    cF
    cE
    tkgeom.p
    tkgeom.d
    tkgeom.i
    tkgeom.g
    tgcgrextend.e
    tgcgrextend.f
    tgcgrextend.e
    wph
    cE
    cE
    c.mi
    co
    cE
    cF
    c.mi
    co
    wph
    cD
    cA
    cE
    cP
    cE
    cG
    cI
    c.mi
    cF
    cD
    cA
    cE
    tkgeom.p
    tkgeom.d
    tkgeom.i
    tkgeom.g
    tgcgrextend.d
    tgcgrextend.a
    tgcgrextend.e
    tgcgrextend.d
    tgcgrextend.a
    tgcgrextend.e
    tgcgrextend.e
    tgcgrextend.f
    tgsegconeq.1
    tgsegconeq.2
    tgsegconeq.2
    wph
    cD
    cA
    c.mi
    co
    eqidd
    #
    wph
    cA
    cE
    c.mi
    co
    #
    eqidd
    wph
    cD
    cA
    cE
    cD
    cP
    cA
    cF
    cG
    cI
    c.mi
    tkgeom.p
    tkgeom.d
    tkgeom.i
    tkgeom.g
    tgcgrextend.d
    tgcgrextend.a
    tgcgrextend.e
    tgcgrextend.d
    tgcgrextend.a
    tgcgrextend.f
    tgsegconeq.2
    tgsegconeq.3
    @0
    wph
    @1
    cB
    cC
    c.mi
    co
    cA
    cF
    c.mi
    co
    tgsegconeq.4
    tgsegconeq.5
    eqtr4d
    #
    tgcgrextend
    @2
    axtg5seg
    eqcomd
    axtgcgrid
end
