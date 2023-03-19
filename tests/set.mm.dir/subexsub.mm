include "caddc.mm"
include "co.mm"
include "wceq.mm"
include "cmin.mm"
include "addlsub.mm"
include "addrsub.mm"
include "bitr3d.mm"

theorem subexsub
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  assume addlsub.a: |- ( ph -> A e. CC )
  assume addlsub.b: |- ( ph -> B e. CC )
  assume addlsub.c: |- ( ph -> C e. CC )


  assert |- ( ph -> ( A = ( C - B ) <-> B = ( C - A ) ) )

  proof
    wph
    cA
    cB
    caddc
    co
    cC
    wceq
    cA
    cC
    cB
    cmin
    co
    wceq
    cB
    cC
    cA
    cmin
    co
    wceq
    wph
    cA
    cB
    cC
    addlsub.a
    addlsub.b
    addlsub.c
    addlsub
    wph
    cA
    cB
    cC
    addlsub.a
    addlsub.b
    addlsub.c
    addrsub
    bitr3d
end
