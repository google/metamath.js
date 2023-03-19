include "wcel.mm"
include "wa.mm"
include "crab.mm"
include "jca.mm"
include "elrab.mm"
include "sylibr.mm"

theorem elrabd
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let cA: class A
  let cB: class B
  assume elrabd.1: |- ( x = A -> ( ps <-> ch ) )
  assume elrabd.2: |- ( ph -> A e. B )
  assume elrabd.3: |- ( ph -> ch )

  disjoint A x
  disjoint B x
  disjoint ch x
  assert |- ( ph -> A e. { x e. B | ps } )

  proof
    wph
    cA
    cB
    wcel
    #
    wch
    wa
    cA
    wps
    vx
    cB
    crab
    wcel
    wph
    @0
    wch
    elrabd.2
    elrabd.3
    jca
    wps
    wch
    vx
    cA
    cB
    elrabd.1
    elrab
    sylibr
end
