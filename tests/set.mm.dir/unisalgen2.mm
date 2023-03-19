include "csalg.mm"
include "wcel.mm"
include "cuni.mm"
include "wceq.mm"
include "wss.mm"
include "w3a.mm"
include "cv.mm"
include "wa.mm"
include "wi.mm"
include "wral.mm"
include "csalgen.mm"
include "cfv.mm"
include "eqcomi.mm"
include "a1i.mm"
include "dfsalgen2.mm"
include "mpbid.mm"
include "simpld.mm"
include "simp2d.mm"

theorem unisalgen2
  let wph: wff ph
  let cA: class A
  let cS: class S
  let cV: class V
  let vx: setvar x
  let vk: setvar k
  assume unisalgen2.x: |- ( ph -> A e. V )
  assume unisalgen2.s: |- S = ( SalGen ` A )


  assert |- ( ph -> U. S = U. A )

  proof
    wph
    cS
    csalg
    wcel
    #
    cS
    cuni
    cA
    cuni
    #
    wceq
    #
    cA
    cS
    wss
    #
    wph
    @0
    @2
    @3
    w3a
    #
    vx
    cv
    #
    cuni
    @1
    wceq
    cA
    @5
    wss
    wa
    cS
    @5
    wss
    wi
    vx
    csalg
    wral
    #
    wph
    cA
    csalgen
    cfv
    #
    cS
    wceq
    #
    @4
    @6
    wa
    @8
    wph
    cS
    @7
    unisalgen2.s
    eqcomi
    a1i
    wph
    vx
    cS
    cV
    cA
    unisalgen2.x
    dfsalgen2
    mpbid
    simpld
    simp2d
end
