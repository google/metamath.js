include "c0.mm"
include "wne.mm"
include "wa.mm"
include "cuni.mm"
include "cint.mm"
include "cwun.mm"
include "wcel.mm"
include "adantr.mm"
include "wununi.mm"
include "wss.mm"
include "intssuni.mm"
include "adantl.mm"
include "wunss.mm"

theorem wunint
  let wph: wff ph
  let cA: class A
  let cU: class U
  let vx: setvar x
  let vy: setvar y
  let cB: class B
  let vu: setvar u
  assume wununi.1: |- ( ph -> U e. WUni )
  assume wununi.2: |- ( ph -> A e. U )


  assert |- ( ( ph /\ A =/= (/) ) -> |^| A e. U )

  proof
    wph
    cA
    c0
    wne
    #
    wa
    cA
    cuni
    #
    cA
    cint
    #
    cU
    wph
    cU
    cwun
    wcel
    @0
    wununi.1
    adantr
    wph
    @1
    cU
    wcel
    @0
    wph
    cA
    cU
    wununi.1
    wununi.2
    wununi
    adantr
    @0
    @2
    @1
    wss
    wph
    cA
    intssuni
    adantl
    wunss
end
