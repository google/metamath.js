include "wb.mm"
include "wral.mm"
include "wi.mm"
include "wa.mm"
include "dfbi2.mm"
include "ralbii.mm"
include "r19.26.mm"
include "bitri.mm"

theorem ralbiim
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cA: class A


  assert |- ( A. x e. A ( ph <-> ps ) <-> ( A. x e. A ( ph -> ps ) /\ A. x e. A ( ps -> ph ) ) )

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
    wi
    #
    wps
    wph
    wi
    #
    wa
    #
    vx
    cA
    wral
    @1
    vx
    cA
    wral
    @2
    vx
    cA
    wral
    wa
    @0
    @3
    vx
    cA
    wph
    wps
    dfbi2
    ralbii
    @1
    @2
    vx
    cA
    r19.26
    bitri
end
