include "rexrd.mm"
include "xrlttri5d.mm"

theorem lttri5d
  let wph: wff ph
  let cA: class A
  let cB: class B
  assume lttri5d.a: |- ( ph -> A e. RR )
  assume lttri5d.b: |- ( ph -> B e. RR )
  assume lttri5d.aneb: |- ( ph -> A =/= B )
  assume lttri5d.nlt: |- ( ph -> -. B < A )


  assert |- ( ph -> A < B )

  proof
    wph
    cA
    cB
    wph
    cA
    lttri5d.a
    rexrd
    wph
    cB
    lttri5d.b
    rexrd
    lttri5d.aneb
    lttri5d.nlt
    xrlttri5d
end
