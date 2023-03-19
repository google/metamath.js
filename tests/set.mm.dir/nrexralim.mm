include "wn.mm"
include "wa.mm"
include "wrex.mm"
include "wral.mm"
include "wi.mm"
include "rexanali.mm"
include "ralbii.mm"
include "ralnex.mm"
include "bitr2i.mm"

theorem nrexralim
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B


  assert |- ( -. E. x e. A A. y e. B ( ph -> ps ) <-> A. x e. A E. y e. B ( ph /\ -. ps ) )

  proof
    wph
    wps
    wn
    wa
    vy
    cB
    wrex
    #
    vx
    cA
    wral
    wph
    wps
    wi
    vy
    cB
    wral
    #
    wn
    #
    vx
    cA
    wral
    @1
    vx
    cA
    wrex
    wn
    @0
    @2
    vx
    cA
    wph
    wps
    vy
    cB
    rexanali
    ralbii
    @1
    vx
    cA
    ralnex
    bitr2i
end
