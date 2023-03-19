include "cdm.mm"
include "ccnv.mm"
include "c0.mm"
include "csn.mm"
include "cun.mm"
include "crn.mm"
include "cxp.mm"
include "ctpos.mm"
include "wundm.mm"
include "wuncnv.mm"
include "wun0.mm"
include "wunsn.mm"
include "wunun.mm"
include "wunrn.mm"
include "wunxp.mm"
include "wss.mm"
include "tposssxp.mm"
include "a1i.mm"
include "wunss.mm"

theorem wuntpos
  let wph: wff ph
  let cA: class A
  let cU: class U
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume wun0.1: |- ( ph -> U e. WUni )
  assume wunop.2: |- ( ph -> A e. U )


  assert |- ( ph -> tpos A e. U )

  proof
    wph
    cA
    cdm
    #
    ccnv
    #
    c0
    csn
    #
    cun
    #
    cA
    crn
    #
    cxp
    #
    cA
    ctpos
    #
    cU
    wun0.1
    wph
    @3
    @4
    cU
    wun0.1
    wph
    @1
    @2
    cU
    wun0.1
    wph
    @0
    cU
    wun0.1
    wph
    cA
    cU
    wun0.1
    wunop.2
    wundm
    wuncnv
    wph
    c0
    cU
    wun0.1
    wph
    cU
    wun0.1
    wun0
    wunsn
    wunun
    wph
    cA
    cU
    wun0.1
    wunop.2
    wunrn
    wunxp
    @6
    @5
    wss
    wph
    cA
    tposssxp
    a1i
    wunss
end
