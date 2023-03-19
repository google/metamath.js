include "wsb.mm"
include "weq.mm"
include "wa.mm"
include "wex.mm"
include "sbid2v.mm"
include "sb5.mm"
include "bitr3i.mm"

theorem sbelx
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y

  disjoint x y
  disjoint ph x
  assert |- ( ph <-> E. x ( x = y /\ [ x / y ] ph ) )

  proof
    wph
    wph
    vy
    vx
    wsb
    #
    vx
    vy
    wsb
    vx
    vy
    weq
    @0
    wa
    vx
    wex
    wph
    vx
    vy
    sbid2v
    @0
    vx
    vy
    sb5
    bitr3i
end
