include "rspcegf.mm"

theorem rspcef
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cA: class A
  let cB: class B
  assume rspcef.1: |- F/ x ps
  assume rspcef.2: |- F/_ x A
  assume rspcef.3: |- F/_ x B
  assume rspcef.4: |- ( x = A -> ( ph <-> ps ) )


  assert |- ( ( A e. B /\ ps ) -> E. x e. B ph )

  proof
    wph
    wps
    vx
    cA
    cB
    rspcef.1
    rspcef.2
    rspcef.3
    rspcef.4
    rspcegf
end
