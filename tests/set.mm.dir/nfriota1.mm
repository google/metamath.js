include "crio.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "cio.mm"
include "df-riota.mm"
include "nfiota1.mm"
include "nfcxfr.mm"

theorem nfriota1
  let wph: wff ph
  let vx: setvar x
  let cA: class A

  disjoint A x
  assert |- F/_ x ( iota_ x e. A ph )

  proof
    vx
    wph
    vx
    cA
    crio
    vx
    cv
    cA
    wcel
    wph
    wa
    #
    vx
    cio
    wph
    vx
    cA
    df-riota
    @0
    vx
    nfiota1
    nfcxfr
end
