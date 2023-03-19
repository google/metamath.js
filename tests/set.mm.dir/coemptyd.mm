include "cdm.mm"
include "crn.mm"
include "cin.mm"
include "c0.mm"
include "wceq.mm"
include "ccom.mm"
include "coeq0.mm"
include "sylibr.mm"

theorem coemptyd
  let wph: wff ph
  let cA: class A
  let cB: class B
  assume coemptyd.1: |- ( ph -> ( dom A i^i ran B ) = (/) )


  assert |- ( ph -> ( A o. B ) = (/) )

  proof
    wph
    cA
    cdm
    cB
    crn
    cin
    c0
    wceq
    cA
    cB
    ccom
    c0
    wceq
    coemptyd.1
    cA
    cB
    coeq0
    sylibr
end
