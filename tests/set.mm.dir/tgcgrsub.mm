include "tgcgrtriv.mm"
include "tgcgrcomlr.mm"
include "tgifscgr.mm"

theorem tgcgrsub
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
  assume tgbtwncgr.p: |- P = ( Base ` G )
  assume tgbtwncgr.m: |- .- = ( dist ` G )
  assume tgbtwncgr.i: |- I = ( Itv ` G )
  assume tgbtwncgr.g: |- ( ph -> G e. TarskiG )
  assume tgbtwncgr.a: |- ( ph -> A e. P )
  assume tgbtwncgr.b: |- ( ph -> B e. P )
  assume tgbtwncgr.c: |- ( ph -> C e. P )
  assume tgbtwncgr.d: |- ( ph -> D e. P )
  assume tgcgrsub.e: |- ( ph -> E e. P )
  assume tgcgrsub.f: |- ( ph -> F e. P )
  assume tgcgrsub.1: |- ( ph -> B e. ( A I C ) )
  assume tgcgrsub.2: |- ( ph -> E e. ( D I F ) )
  assume tgcgrsub.3: |- ( ph -> ( A .- C ) = ( D .- F ) )
  assume tgcgrsub.4: |- ( ph -> ( B .- C ) = ( E .- F ) )


  assert |- ( ph -> ( A .- B ) = ( D .- E ) )

  proof
    wph
    cB
    cA
    cE
    cD
    cP
    cG
    cI
    c.mi
    tgbtwncgr.p
    tgbtwncgr.m
    tgbtwncgr.i
    tgbtwncgr.g
    tgbtwncgr.b
    tgbtwncgr.a
    tgcgrsub.e
    tgbtwncgr.d
    wph
    cA
    cB
    cC
    cA
    cP
    cD
    cE
    cG
    cD
    cI
    cF
    c.mi
    tgbtwncgr.p
    tgbtwncgr.m
    tgbtwncgr.i
    tgbtwncgr.g
    tgbtwncgr.a
    tgbtwncgr.b
    tgbtwncgr.c
    tgbtwncgr.a
    tgbtwncgr.d
    tgcgrsub.e
    tgcgrsub.f
    tgbtwncgr.d
    tgcgrsub.1
    tgcgrsub.2
    tgcgrsub.3
    tgcgrsub.4
    wph
    cA
    cD
    cP
    cG
    cI
    c.mi
    tgbtwncgr.p
    tgbtwncgr.m
    tgbtwncgr.i
    tgbtwncgr.g
    tgbtwncgr.a
    tgbtwncgr.d
    tgcgrtriv
    wph
    cA
    cC
    cD
    cF
    cP
    cG
    cI
    c.mi
    tgbtwncgr.p
    tgbtwncgr.m
    tgbtwncgr.i
    tgbtwncgr.g
    tgbtwncgr.a
    tgbtwncgr.c
    tgbtwncgr.d
    tgcgrsub.f
    tgcgrsub.3
    tgcgrcomlr
    tgifscgr
    tgcgrcomlr
end
