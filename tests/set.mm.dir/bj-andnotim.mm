include "wn.mm"
include "wa.mm"
include "wi.mm"
include "wo.mm"
include "imor.mm"
include "iman.mm"
include "biimpri.mm"
include "orim1i.mm"
include "sylbi.mm"
include "pm2.24.mm"
include "imim2i.mm"
include "impd.mm"
include "ax-1.mm"
include "jaoi.mm"
include "impbii.mm"

theorem bj-andnotim
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch


  assert |- ( ( ( ph /\ -. ps ) -> ch ) <-> ( ( ph -> ps ) \/ ch ) )

  proof
    wph
    wps
    wn
    #
    wa
    #
    wch
    wi
    #
    wph
    wps
    wi
    #
    wch
    wo
    #
    @2
    @1
    wn
    #
    wch
    wo
    @4
    @1
    wch
    imor
    @5
    @3
    wch
    @3
    @5
    wph
    wps
    iman
    biimpri
    orim1i
    sylbi
    @3
    @2
    wch
    @3
    wph
    @0
    wch
    wps
    @0
    wch
    wi
    wph
    wps
    wch
    pm2.24
    imim2i
    impd
    wch
    @1
    ax-1
    jaoi
    impbii
end
