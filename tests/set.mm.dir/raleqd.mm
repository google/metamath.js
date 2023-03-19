include "wceq.mm"
include "wral.mm"
include "wb.mm"
include "raleqf.mm"
include "syl.mm"

theorem raleqd
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cA: class A
  let cB: class B
  assume raleqd.a: |- F/_ x A
  assume raleqd.b: |- F/_ x B
  assume raleqd.e: |- ( ph -> A = B )


  assert |- ( ph -> ( A. x e. A ps <-> A. x e. B ps ) )

  proof
    wph
    cA
    cB
    wceq
    wps
    vx
    cA
    wral
    wps
    vx
    cB
    wral
    wb
    raleqd.e
    wps
    vx
    cA
    cB
    raleqd.a
    raleqd.b
    raleqf
    syl
end
