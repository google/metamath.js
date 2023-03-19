include "co.mm"
include "axtgcgrrflx.mm"
include "3eqtr3d.mm"

theorem tgcgrcomlr
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
  assume tgcgrcomlr.a: |- ( ph -> A e. P )
  assume tgcgrcomlr.b: |- ( ph -> B e. P )
  assume tgcgrcomlr.c: |- ( ph -> C e. P )
  assume tgcgrcomlr.d: |- ( ph -> D e. P )
  assume tgcgrcomlr.6: |- ( ph -> ( A .- B ) = ( C .- D ) )


  assert |- ( ph -> ( B .- A ) = ( D .- C ) )

  proof
    wph
    cA
    cB
    c.mi
    co
    cC
    cD
    c.mi
    co
    cB
    cA
    c.mi
    co
    cD
    cC
    c.mi
    co
    tgcgrcomlr.6
    wph
    cP
    cG
    cI
    c.mi
    cA
    cB
    tkgeom.p
    tkgeom.d
    tkgeom.i
    tkgeom.g
    tgcgrcomlr.a
    tgcgrcomlr.b
    axtgcgrrflx
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
    tgcgrcomlr.c
    tgcgrcomlr.d
    axtgcgrrflx
    3eqtr3d
end
