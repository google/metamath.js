include "cid.mm"
include "wfun.mm"
include "wcel.mm"
include "cres.mm"
include "cvv.mm"
include "funi.mm"
include "resfunexg.mm"
include "sylancr.mm"

theorem resiexd
  let wph: wff ph
  let cB: class B
  let cV: class V
  assume resiexd.b: |- ( ph -> B e. V )


  assert |- ( ph -> ( _I |` B ) e. _V )

  proof
    wph
    cid
    wfun
    cB
    cV
    wcel
    cid
    cB
    cres
    cvv
    wcel
    funi
    resiexd.b
    cid
    cB
    cV
    resfunexg
    sylancr
end
