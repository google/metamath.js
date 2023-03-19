include "wsbc.mm"
include "wnf.mm"
include "wtru.mm"
include "wnfc.mm"
include "a1i.mm"
include "nfsbc1d.mm"
include "trud.mm"

theorem nfsbc1
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  assume nfsbc1.1: |- F/_ x A


  assert |- F/ x [. A / x ]. ph

  proof
    wph
    vx
    cA
    wsbc
    vx
    wnf
    wtru
    wph
    vx
    cA
    vx
    cA
    wnfc
    wtru
    nfsbc1.1
    a1i
    nfsbc1d
    trud
end
