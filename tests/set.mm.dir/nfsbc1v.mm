include "nfcv.mm"
include "nfsbc1.mm"

theorem nfsbc1v
  let wph: wff ph
  let vx: setvar x
  let cA: class A

  disjoint A x
  assert |- F/ x [. A / x ]. ph

  proof
    wph
    vx
    cA
    vx
    cA
    nfcv
    nfsbc1
end
