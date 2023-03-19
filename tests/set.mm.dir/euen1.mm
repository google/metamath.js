include "cvv.mm"
include "wreu.mm"
include "crab.mm"
include "c1o.mm"
include "cen.mm"
include "wbr.mm"
include "weu.mm"
include "cab.mm"
include "reuen1.mm"
include "reuv.mm"
include "rabab.mm"
include "breq1i.mm"
include "3bitr3i.mm"

theorem euen1
  let wph: wff ph
  let vx: setvar x
  let vf: setvar f
  let vy: setvar y
  let cA: class A


  assert |- ( E! x ph <-> { x | ph } ~~ 1o )

  proof
    wph
    vx
    cvv
    wreu
    wph
    vx
    cvv
    crab
    #
    c1o
    cen
    wbr
    wph
    vx
    weu
    wph
    vx
    cab
    #
    c1o
    cen
    wbr
    wph
    vx
    cvv
    reuen1
    wph
    vx
    reuv
    @0
    @1
    c1o
    cen
    wph
    vx
    rabab
    breq1i
    3bitr3i
end
