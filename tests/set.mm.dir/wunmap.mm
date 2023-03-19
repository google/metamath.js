include "cpm.mm"
include "co.mm"
include "cmap.mm"
include "wunpm.mm"
include "wss.mm"
include "mapsspm.mm"
include "a1i.mm"
include "wunss.mm"

theorem wunmap
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


  assert |- ( ph -> ( A ^m B ) e. U )

  proof
    wph
    cA
    cB
    cpm
    co
    #
    cA
    cB
    cmap
    co
    #
    cU
    wun0.1
    wph
    cA
    cB
    cU
    wun0.1
    wunop.2
    wunop.3
    wunpm
    @1
    @0
    wss
    wph
    cA
    cB
    mapsspm
    a1i
    wunss
end
