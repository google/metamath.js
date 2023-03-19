include "ccom.mm"
include "cdm.mm"
include "crn.mm"
include "cxp.mm"
include "wundm.mm"
include "wss.mm"
include "dmcoss.mm"
include "a1i.mm"
include "wunss.mm"
include "wunrn.mm"
include "rncoss.mm"
include "wunxp.mm"
include "wrel.mm"
include "relco.mm"
include "relssdmrn.mm"
include "mp1i.mm"

theorem wunco
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cU: class U
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume wun0.1: |- ( ph -> U e. WUni )
  assume wunop.2: |- ( ph -> A e. U )
  assume wunco.3: |- ( ph -> B e. U )


  assert |- ( ph -> ( A o. B ) e. U )

  proof
    wph
    cA
    cB
    ccom
    #
    cdm
    #
    @0
    crn
    #
    cxp
    #
    @0
    cU
    wun0.1
    wph
    @1
    @2
    cU
    wun0.1
    wph
    cB
    cdm
    #
    @1
    cU
    wun0.1
    wph
    cB
    cU
    wun0.1
    wunco.3
    wundm
    @1
    @4
    wss
    wph
    cA
    cB
    dmcoss
    a1i
    wunss
    wph
    cA
    crn
    #
    @2
    cU
    wun0.1
    wph
    cA
    cU
    wun0.1
    wunop.2
    wunrn
    @2
    @5
    wss
    wph
    cA
    cB
    rncoss
    a1i
    wunss
    wunxp
    @0
    wrel
    @0
    @3
    wss
    wph
    cA
    cB
    relco
    @0
    relssdmrn
    mp1i
    wunss
end
