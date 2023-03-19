include "wrex.mm"
include "wi.mm"
include "wa.mm"
include "cv.mm"
include "wceq.mm"
include "wb.mm"
include "syldan.mm"
include "biimpd.mm"
include "expcom.mm"
include "pm2.43b.mm"
include "rexlimdvw.mm"
include "rspcedv.mm"
include "impbid.mm"

theorem rspcebdv
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let cA: class A
  let cB: class B
  assume rspcdv.1: |- ( ph -> A e. B )
  assume rspcdv.2: |- ( ( ph /\ x = A ) -> ( ps <-> ch ) )
  assume rspcebdv.1: |- ( ( ph /\ ps ) -> x = A )

  disjoint A x
  disjoint B x
  disjoint ph x
  disjoint ch x
  assert |- ( ph -> ( E. x e. B ps <-> ch ) )

  proof
    wph
    wps
    vx
    cB
    wrex
    wch
    wph
    wps
    wch
    vx
    cB
    wph
    wps
    wch
    wph
    wps
    wps
    wch
    wi
    wph
    wps
    wa
    wps
    wch
    wph
    wps
    vx
    cv
    cA
    wceq
    wps
    wch
    wb
    rspcebdv.1
    rspcdv.2
    syldan
    biimpd
    expcom
    pm2.43b
    rexlimdvw
    wph
    wps
    wch
    vx
    cA
    cB
    rspcdv.1
    rspcdv.2
    rspcedv
    impbid
end
