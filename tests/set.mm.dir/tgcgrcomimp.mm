include "co.mm"
include "wceq.mm"
include "axtgcgrrflx.mm"
include "eqeq2d.mm"
include "biimpd.mm"

theorem tgcgrcomimp
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cP: class P
  let cG: class G
  let cI: class I
  let c.mi: class .-
  assume tkgeom.p: |- P = ( Base ` G )
  assume tkgeom.d: |- .- = ( dist ` G )
  assume tkgeom.i: |- I = ( Itv ` G )
  assume tkgeom.g: |- ( ph -> G e. TarskiG )
  assume tgcgrcomimp.a: |- ( ph -> A e. P )
  assume tgcgrcomimp.b: |- ( ph -> B e. P )
  assume tgcgrcomimp.c: |- ( ph -> C e. P )
  assume tgcgrcomimp.d: |- ( ph -> D e. P )


  assert |- ( ph -> ( ( A .- B ) = ( C .- D ) -> ( A .- B ) = ( D .- C ) ) )

  proof
    wph
    cA
    cB
    c.mi
    co
    #
    cC
    cD
    c.mi
    co
    #
    wceq
    @0
    cD
    cC
    c.mi
    co
    #
    wceq
    wph
    @1
    @2
    @0
    wph
    cP
    cG
    cI
    c.mi
    cC
    cD
    tkgeom.p
    tkgeom.d
    tkgeom.i
    tkgeom.g
    tgcgrcomimp.c
    tgcgrcomimp.d
    axtgcgrrflx
    eqeq2d
    biimpd
end
