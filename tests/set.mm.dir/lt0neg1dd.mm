include "cc0.mm"
include "clt.mm"
include "wbr.mm"
include "cneg.mm"
include "lt0neg1d.mm"
include "mpbid.mm"

theorem lt0neg1dd
  let wph: wff ph
  let cA: class A
  assume lt0neg1dd.1: |- ( ph -> A e. RR )
  assume lt0neg1dd.2: |- ( ph -> A < 0 )


  assert |- ( ph -> 0 < -u A )

  proof
    wph
    cA
    cc0
    clt
    wbr
    cc0
    cA
    cneg
    clt
    wbr
    lt0neg1dd.2
    wph
    cA
    lt0neg1dd.1
    lt0neg1d
    mpbid
end
