include "wtr.mm"
include "wcel.mm"
include "trel.mm"
include "3impib.mm"
include "syl3an.mm"

theorem trelded
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let cA: class A
  let cB: class B
  let cC: class C
  assume trelded.1: |- ( ph -> Tr A )
  assume trelded.2: |- ( ps -> B e. C )
  assume trelded.3: |- ( ch -> C e. A )


  assert |- ( ( ph /\ ps /\ ch ) -> B e. A )

  proof
    wph
    cA
    wtr
    #
    wps
    cB
    cC
    wcel
    #
    wch
    cC
    cA
    wcel
    #
    cB
    cA
    wcel
    #
    trelded.1
    trelded.2
    trelded.3
    @0
    @1
    @2
    @3
    cA
    cB
    cC
    trel
    3impib
    syl3an
end
