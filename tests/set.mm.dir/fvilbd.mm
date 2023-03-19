include "cid.mm"
include "cfv.mm"
include "ssid.mm"
include "cvv.mm"
include "wcel.mm"
include "wceq.mm"
include "fvi.mm"
include "syl.mm"
include "syl5sseqr.mm"

theorem fvilbd
  let wph: wff ph
  let cR: class R
  assume fvilbd.r: |- ( ph -> R e. _V )


  assert |- ( ph -> R C_ ( _I ` R ) )

  proof
    wph
    cR
    cR
    cR
    cid
    cfv
    #
    cR
    ssid
    wph
    cR
    cvv
    wcel
    @0
    cR
    wceq
    fvilbd.r
    cR
    cvv
    fvi
    syl
    syl5sseqr
end
