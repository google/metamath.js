include "cbs.mm"
include "tgldim0eq.mm"
include "oveq12d.mm"

theorem tgldim0cgr
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cP: class P
  let cG: class G
  let cI: class I
  let c.mi: class .-
  assume tgbtwndiff.p: |- P = ( Base ` G )
  assume tgbtwndiff.d: |- .- = ( dist ` G )
  assume tgbtwndiff.i: |- I = ( Itv ` G )
  assume tgbtwndiff.g: |- ( ph -> G e. TarskiG )
  assume tgbtwndiff.a: |- ( ph -> A e. P )
  assume tgbtwndiff.b: |- ( ph -> B e. P )
  assume tgldim0itv.c: |- ( ph -> C e. P )
  assume tgldim0itv.p: |- ( ph -> ( # ` P ) = 1 )
  assume tgldim0itv.d: |- ( ph -> D e. P )


  assert |- ( ph -> ( A .- B ) = ( C .- D ) )

  proof
    wph
    cA
    cC
    cB
    cD
    c.mi
    wph
    cA
    cC
    cP
    cbs
    cG
    tgbtwndiff.p
    tgldim0itv.p
    tgbtwndiff.a
    tgldim0itv.c
    tgldim0eq
    wph
    cB
    cD
    cP
    cbs
    cG
    tgbtwndiff.p
    tgldim0itv.p
    tgbtwndiff.b
    tgldim0itv.d
    tgldim0eq
    oveq12d
end
