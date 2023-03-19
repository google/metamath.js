include "wnfc.mm"
include "nfceqi.mm"
include "sylibr.mm"

theorem nfcxfrd
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  assume nfceqi.1: |- A = B
  assume nfcxfrd.2: |- ( ph -> F/_ x B )


  assert |- ( ph -> F/_ x A )

  proof
    wph
    vx
    cB
    wnfc
    vx
    cA
    wnfc
    nfcxfrd.2
    vx
    cA
    cB
    nfceqi.1
    nfceqi
    sylibr
end
