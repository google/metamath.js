include "cneg.mm"
include "wceq.mm"
include "neg11ad.mm"
include "mpbid.mm"

theorem neg11d
  let wph: wff ph
  let cA: class A
  let cB: class B
  assume negidd.1: |- ( ph -> A e. CC )
  assume pncand.2: |- ( ph -> B e. CC )
  assume neg11d.3: |- ( ph -> -u A = -u B )


  assert |- ( ph -> A = B )

  proof
    wph
    cA
    cneg
    cB
    cneg
    wceq
    cA
    cB
    wceq
    neg11d.3
    wph
    cA
    cB
    negidd.1
    pncand.2
    neg11ad
    mpbid
end
