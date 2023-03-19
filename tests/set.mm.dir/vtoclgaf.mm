include "wcel.mm"
include "cv.mm"
include "wi.mm"
include "nfel1.mm"
include "nfim.mm"
include "wceq.mm"
include "eleq1.mm"
include "imbi12d.mm"
include "vtoclgf.mm"
include "pm2.43i.mm"

theorem vtoclgaf
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cA: class A
  let cB: class B
  assume vtoclgaf.1: |- F/_ x A
  assume vtoclgaf.2: |- F/ x ps
  assume vtoclgaf.3: |- ( x = A -> ( ph <-> ps ) )
  assume vtoclgaf.4: |- ( x e. B -> ph )

  disjoint B x
  assert |- ( A e. B -> ps )

  proof
    cA
    cB
    wcel
    #
    wps
    vx
    cv
    #
    cB
    wcel
    #
    wph
    wi
    @0
    wps
    wi
    vx
    cA
    cB
    vtoclgaf.1
    @0
    wps
    vx
    vx
    cA
    cB
    vtoclgaf.1
    nfel1
    vtoclgaf.2
    nfim
    @1
    cA
    wceq
    @2
    @0
    wph
    wps
    @1
    cA
    cB
    eleq1
    vtoclgaf.3
    imbi12d
    vtoclgaf.4
    vtoclgf
    pm2.43i
end
