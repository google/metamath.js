include "co.mm"
include "axtgcgrrflx.mm"
include "eqtr3d.mm"

theorem tgcgrcoml
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
  assume tgcgrcomr.a: |- ( ph -> A e. P )
  assume tgcgrcomr.b: |- ( ph -> B e. P )
  assume tgcgrcomr.c: |- ( ph -> C e. P )
  assume tgcgrcomr.d: |- ( ph -> D e. P )
  assume tgcgrcomr.6: |- ( ph -> ( A .- B ) = ( C .- D ) )


  assert |- ( ph -> ( B .- A ) = ( C .- D ) )

  proof
    wph
    cA
    cB
    c.mi
    co
    cB
    cA
    c.mi
    co
    cC
    cD
    c.mi
    co
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
    tgcgrcomr.a
    tgcgrcomr.b
    axtgcgrrflx
    tgcgrcomr.6
    eqtr3d
end
