include "cneg.mm"
include "cc0.mm"
include "cmin.mm"
include "co.mm"
include "df-neg.mm"
include "nfcvd.mm"
include "nfovd.mm"
include "nfcxfrd.mm"

theorem nfnegd
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  assume nfnegd.1: |- ( ph -> F/_ x A )


  assert |- ( ph -> F/_ x -u A )

  proof
    wph
    vx
    cA
    cneg
    cc0
    cA
    cmin
    co
    cA
    df-neg
    wph
    vx
    cc0
    cA
    cmin
    wph
    vx
    cc0
    nfcvd
    wph
    vx
    cmin
    nfcvd
    nfnegd.1
    nfovd
    nfcxfrd
end
