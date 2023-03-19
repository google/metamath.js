include "wnfc.mm"
include "nfceqdf.mm"
include "mpbird.mm"

theorem nfcxfrdf
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  assume nfcxfrdf.0: |- F/ x ph
  assume nfcxfrdf.1: |- ( ph -> A = B )
  assume nfcxfrdf.2: |- ( ph -> F/_ x B )


  assert |- ( ph -> F/_ x A )

  proof
    wph
    vx
    cA
    wnfc
    vx
    cB
    wnfc
    nfcxfrdf.2
    wph
    vx
    cA
    cB
    nfcxfrdf.0
    nfcxfrdf.1
    nfceqdf
    mpbird
end
