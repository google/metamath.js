include "co.mm"
include "cbs.mm"
include "tgldim0eq.mm"
include "tgbtwntriv1.mm"
include "eqeltrd.mm"

theorem tgldim0itv
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
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


  assert |- ( ph -> A e. ( B I C ) )

  proof
    wph
    cA
    cB
    cB
    cC
    cI
    co
    wph
    cA
    cB
    cP
    cbs
    cG
    tgbtwndiff.p
    tgldim0itv.p
    tgbtwndiff.a
    tgbtwndiff.b
    tgldim0eq
    wph
    cB
    cC
    cP
    cG
    cI
    c.mi
    tgbtwndiff.p
    tgbtwndiff.d
    tgbtwndiff.i
    tgbtwndiff.g
    tgbtwndiff.b
    tgldim0itv.c
    tgbtwntriv1
    eqeltrd
end
