include "cop.mm"
include "csn.mm"
include "cpr.mm"
include "wcel.mm"
include "wceq.mm"
include "dfopg.mm"
include "syl2anc.mm"
include "wunsn.mm"
include "wunpr.mm"
include "eqeltrd.mm"

theorem wunop
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cU: class U
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume wun0.1: |- ( ph -> U e. WUni )
  assume wunop.2: |- ( ph -> A e. U )
  assume wunop.3: |- ( ph -> B e. U )


  assert |- ( ph -> <. A , B >. e. U )

  proof
    wph
    cA
    cB
    cop
    #
    cA
    csn
    #
    cA
    cB
    cpr
    #
    cpr
    #
    cU
    wph
    cA
    cU
    wcel
    cB
    cU
    wcel
    @0
    @3
    wceq
    wunop.2
    wunop.3
    cA
    cB
    cU
    cU
    dfopg
    syl2anc
    wph
    @1
    @2
    cU
    wun0.1
    wph
    cA
    cU
    wun0.1
    wunop.2
    wunsn
    wph
    cA
    cB
    cU
    wun0.1
    wunop.2
    wunop.3
    wunpr
    wunpr
    eqeltrd
end
