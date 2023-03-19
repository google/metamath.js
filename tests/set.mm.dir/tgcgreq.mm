include "wceq.mm"
include "tgcgreqb.mm"
include "mpbid.mm"

theorem tgcgreq
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
  assume tgcgreq.1: |- ( ph -> A = B )


  assert |- ( ph -> C = D )

  proof
    wph
    cA
    cB
    wceq
    cC
    cD
    wceq
    tgcgreq.1
    wph
    cA
    cB
    cC
    cD
    cP
    cG
    cI
    c.mi
    tkgeom.p
    tkgeom.d
    tkgeom.i
    tkgeom.g
    tgcgrcomlr.a
    tgcgrcomlr.b
    tgcgrcomlr.c
    tgcgrcomlr.d
    tgcgrcomlr.6
    tgcgreqb
    mpbid
end
