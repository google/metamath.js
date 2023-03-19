include "cmpt.mm"
include "crn.mm"
include "cr.mm"
include "eqid.mm"
include "rnmptssd.mm"
include "rnmptn0.mm"
include "rnmptbdd.mm"
include "suprcld.mm"

theorem suprclrnmpt
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let vz: setvar z
  assume suprclrnmpt.x: |- F/ x ph
  assume suprclrnmpt.n: |- ( ph -> A =/= (/) )
  assume suprclrnmpt.b: |- ( ( ph /\ x e. A ) -> B e. RR )
  assume suprclrnmpt.y: |- ( ph -> E. y e. RR A. x e. A B <_ y )

  disjoint A x
  disjoint A y
  disjoint x y
  disjoint B y
  disjoint A z
  disjoint x z
  disjoint y z
  disjoint B z
  assert |- ( ph -> sup ( ran ( x e. A |-> B ) , RR , < ) e. RR )

  proof
    wph
    vy
    vz
    vx
    cA
    cB
    cmpt
    #
    crn
    wph
    vx
    cA
    cB
    cr
    @0
    suprclrnmpt.x
    @0
    eqid
    #
    suprclrnmpt.b
    rnmptssd
    wph
    vx
    cA
    cB
    @0
    cr
    suprclrnmpt.x
    suprclrnmpt.b
    @1
    suprclrnmpt.n
    rnmptn0
    wph
    vx
    vy
    vz
    cA
    cB
    suprclrnmpt.x
    suprclrnmpt.y
    rnmptbdd
    suprcld
end
