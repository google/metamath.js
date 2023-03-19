include "wb.mm"
include "wral.mm"
include "nfra1.mm"
include "rspa.mm"
include "ralbida.mm"

theorem ralbi
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cA: class A


  assert |- ( A. x e. A ( ph <-> ps ) -> ( A. x e. A ph <-> A. x e. A ps ) )

  proof
    wph
    wps
    wb
    #
    vx
    cA
    wral
    wph
    wps
    vx
    cA
    @0
    vx
    cA
    nfra1
    @0
    vx
    cA
    rspa
    ralbida
end
