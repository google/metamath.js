include "wreu.mm"
include "crio.mm"
include "cuni.mm"
include "cpw.mm"
include "cun.mm"
include "wss.mm"
include "crab.mm"
include "riotauni.mm"
include "ssrab2.mm"
include "unissi.mm"
include "ssun2.mm"
include "sstri.mm"
include "syl6eqss.mm"
include "wn.mm"
include "c0.mm"
include "riotaund.mm"
include "0ss.mm"
include "pm2.61i.mm"

theorem riotassuni
  let wph: wff ph
  let vx: setvar x
  let cA: class A

  disjoint A x
  assert |- ( iota_ x e. A ph ) C_ ( ~P U. A u. U. A )

  proof
    wph
    vx
    cA
    wreu
    #
    wph
    vx
    cA
    crio
    #
    cA
    cuni
    #
    cpw
    #
    @2
    cun
    #
    wss
    @0
    @1
    wph
    vx
    cA
    crab
    #
    cuni
    #
    @4
    wph
    vx
    cA
    riotauni
    @6
    @2
    @4
    @5
    cA
    wph
    vx
    cA
    ssrab2
    unissi
    @2
    @3
    ssun2
    sstri
    syl6eqss
    @0
    wn
    @1
    c0
    @4
    wph
    vx
    cA
    riotaund
    @4
    0ss
    syl6eqss
    pm2.61i
end
