include "cuni.mm"
include "crn.mm"
include "wununi.mm"
include "wss.mm"
include "cdm.mm"
include "cun.mm"
include "ssun2.mm"
include "dmrnssfld.mm"
include "sstri.mm"
include "a1i.mm"
include "wunss.mm"

theorem wunrn
  let wph: wff ph
  let cA: class A
  let cU: class U
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume wun0.1: |- ( ph -> U e. WUni )
  assume wunop.2: |- ( ph -> A e. U )


  assert |- ( ph -> ran A e. U )

  proof
    wph
    cA
    cuni
    #
    cuni
    #
    cA
    crn
    #
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
    wununi
    wununi
    @2
    @1
    wss
    wph
    @2
    cA
    cdm
    #
    @2
    cun
    @1
    @2
    @3
    ssun2
    cA
    dmrnssfld
    sstri
    a1i
    wunss
end
