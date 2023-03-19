include "wral.mm"
include "cv.mm"
include "wcel.mm"
include "wi.mm"
include "wal.mm"
include "df-ral.mm"
include "nfcv.mm"
include "nfv.mm"
include "nfim.mm"
include "wceq.mm"
include "eleq1.mm"
include "imbi12d.mm"
include "spcgf.mm"
include "pm2.43a.mm"
include "syl5bi.mm"

theorem rspc
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cA: class A
  let cB: class B
  assume rspc.1: |- F/ x ps
  assume rspc.2: |- ( x = A -> ( ph <-> ps ) )

  disjoint A x
  disjoint B x
  assert |- ( A e. B -> ( A. x e. B ph -> ps ) )

  proof
    wph
    vx
    cB
    wral
    vx
    cv
    #
    cB
    wcel
    #
    wph
    wi
    #
    vx
    wal
    #
    cA
    cB
    wcel
    #
    wps
    wph
    vx
    cB
    df-ral
    @3
    @4
    wps
    @2
    @4
    wps
    wi
    vx
    cA
    cB
    vx
    cA
    nfcv
    @4
    wps
    vx
    @4
    vx
    nfv
    rspc.1
    nfim
    @0
    cA
    wceq
    @1
    @4
    wph
    wps
    @0
    cA
    cB
    eleq1
    rspc.2
    imbi12d
    spcgf
    pm2.43a
    syl5bi
end
