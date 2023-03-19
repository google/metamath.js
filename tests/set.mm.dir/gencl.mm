include "wceq.mm"
include "wa.mm"
include "wex.mm"
include "syl5ib.mm"
include "impcom.mm"
include "exlimiv.mm"
include "sylbi.mm"

theorem gencl
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let vx: setvar x
  let cA: class A
  let cB: class B
  assume gencl.1: |- ( th <-> E. x ( ch /\ A = B ) )
  assume gencl.2: |- ( A = B -> ( ph <-> ps ) )
  assume gencl.3: |- ( ch -> ph )

  disjoint ps x
  assert |- ( th -> ps )

  proof
    wth
    wch
    cA
    cB
    wceq
    #
    wa
    #
    vx
    wex
    wps
    gencl.1
    @1
    wps
    vx
    @0
    wch
    wps
    wch
    wph
    @0
    wps
    gencl.3
    gencl.2
    syl5ib
    impcom
    exlimiv
    sylbi
end
