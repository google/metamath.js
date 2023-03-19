include "co.mm"
include "axtgcgrrflx.mm"
include "eqtrd.mm"

theorem tgcgrcomr
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


  assert |- ( ph -> ( A .- B ) = ( D .- C ) )

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
    cD
    cC
    c.mi
    co
    tgcgrcomr.6
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
    tgcgrcomr.c
    tgcgrcomr.d
    axtgcgrrflx
    eqtrd
end
