include "crn.mm"
include "cdm.mm"
include "cxp.mm"
include "ccnv.mm"
include "wunrn.mm"
include "wundm.mm"
include "wunxp.mm"
include "wss.mm"
include "cnvssrndm.mm"
include "a1i.mm"
include "wunss.mm"

theorem wuncnv
  let wph: wff ph
  let cA: class A
  let cU: class U
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume wun0.1: |- ( ph -> U e. WUni )
  assume wunop.2: |- ( ph -> A e. U )


  assert |- ( ph -> `' A e. U )

  proof
    wph
    cA
    crn
    #
    cA
    cdm
    #
    cxp
    #
    cA
    ccnv
    #
    cU
    wun0.1
    wph
    @0
    @1
    cU
    wun0.1
    wph
    cA
    cU
    wun0.1
    wunop.2
    wunrn
    wph
    cA
    cU
    wun0.1
    wunop.2
    wundm
    wunxp
    @3
    @2
    wss
    wph
    cA
    cnvssrndm
    a1i
    wunss
end
