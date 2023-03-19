include "cpr.mm"
include "cuni.mm"
include "cun.mm"
include "wcel.mm"
include "wceq.mm"
include "uniprg.mm"
include "syl2anc.mm"
include "wunpr.mm"
include "wununi.mm"
include "eqeltrrd.mm"

theorem wunun
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cU: class U
  let vx: setvar x
  let vy: setvar y
  let vu: setvar u
  assume wununi.1: |- ( ph -> U e. WUni )
  assume wununi.2: |- ( ph -> A e. U )
  assume wunpr.3: |- ( ph -> B e. U )


  assert |- ( ph -> ( A u. B ) e. U )

  proof
    wph
    cA
    cB
    cpr
    #
    cuni
    #
    cA
    cB
    cun
    #
    cU
    wph
    cA
    cU
    wcel
    cB
    cU
    wcel
    @1
    @2
    wceq
    wununi.2
    wunpr.3
    cA
    cB
    cU
    cU
    uniprg
    syl2anc
    wph
    @0
    cU
    wununi.1
    wph
    cA
    cB
    cU
    wununi.1
    wununi.2
    wunpr.3
    wunpr
    wununi
    eqeltrrd
end
