include "wcel.mm"
include "wral.mm"
include "cmpt.mm"
include "crn.mm"
include "wb.mm"
include "ralrimia.mm"
include "eqid.mm"
include "ralrnmpt.mm"
include "syl.mm"

theorem ralrnmpt3
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cV: class V
  assume ralrnmpt3.1: |- F/ x ph
  assume ralrnmpt3.2: |- ( ( ph /\ x e. A ) -> B e. V )
  assume ralrnmpt3.3: |- ( y = B -> ( ps <-> ch ) )

  disjoint A x
  disjoint A y
  disjoint x y
  disjoint B y
  disjoint ch y
  disjoint ps x
  assert |- ( ph -> ( A. y e. ran ( x e. A |-> B ) ps <-> A. x e. A ch ) )

  proof
    wph
    cB
    cV
    wcel
    #
    vx
    cA
    wral
    wps
    vy
    vx
    cA
    cB
    cmpt
    #
    crn
    wral
    wch
    vx
    cA
    wral
    wb
    wph
    @0
    vx
    cA
    ralrnmpt3.1
    ralrnmpt3.2
    ralrimia
    wps
    wch
    vx
    vy
    cA
    cB
    @1
    cV
    @1
    eqid
    ralrnmpt3.3
    ralrnmpt
    syl
end
