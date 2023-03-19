include "cv.mm"
include "wceq.mm"
include "wb.mm"
include "wi.mm"
include "wal.mm"
include "wcel.mm"
include "wral.mm"
include "df-ral.mm"
include "wa.mm"
include "eleq1.mm"
include "adantr.mm"
include "simpr.mm"
include "imbi12d.mm"
include "ex.mm"
include "a2i.mm"
include "alimi.mm"
include "nfv.mm"
include "nfim.mm"
include "nfcv.mm"
include "spcgft.mm"
include "syl.mm"
include "syl7bi.mm"
include "com34.mm"
include "pm2.43d.mm"

theorem rspct
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cA: class A
  let cB: class B
  assume rspct.1: |- F/ x ps

  disjoint A x
  disjoint B x
  assert |- ( A. x ( x = A -> ( ph <-> ps ) ) -> ( A e. B -> ( A. x e. B ph -> ps ) ) )

  proof
    vx
    cv
    #
    cA
    wceq
    #
    wph
    wps
    wb
    #
    wi
    #
    vx
    wal
    #
    cA
    cB
    wcel
    #
    wph
    vx
    cB
    wral
    #
    wps
    wi
    @4
    @5
    @6
    @5
    wps
    @6
    @0
    cB
    wcel
    #
    wph
    wi
    #
    vx
    wal
    #
    @4
    @5
    @5
    wps
    wi
    #
    wph
    vx
    cB
    df-ral
    @4
    @1
    @8
    @10
    wb
    #
    wi
    #
    vx
    wal
    @5
    @9
    @10
    wi
    wi
    @3
    @12
    vx
    @1
    @2
    @11
    @1
    @2
    @11
    @1
    @2
    wa
    @7
    @5
    wph
    wps
    @1
    @7
    @5
    wb
    @2
    @0
    cA
    cB
    eleq1
    adantr
    @1
    @2
    simpr
    imbi12d
    ex
    a2i
    alimi
    @8
    @10
    vx
    cA
    cB
    @5
    wps
    vx
    @5
    vx
    nfv
    rspct.1
    nfim
    vx
    cA
    nfcv
    spcgft
    syl
    syl7bi
    com34
    pm2.43d
end
