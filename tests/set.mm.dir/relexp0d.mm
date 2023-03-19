include "cvv.mm"
include "wcel.mm"
include "wrel.mm"
include "cc0.mm"
include "crelexp.mm"
include "co.mm"
include "cid.mm"
include "cuni.mm"
include "cres.mm"
include "wceq.mm"
include "relexp0.mm"
include "syl2anc.mm"

theorem relexp0d
  let wph: wff ph
  let cR: class R
  assume relexp0d.1: |- ( ph -> Rel R )
  assume relexp0d.2: |- ( ph -> R e. _V )


  assert |- ( ph -> ( R ^r 0 ) = ( _I |` U. U. R ) )

  proof
    wph
    cR
    cvv
    wcel
    cR
    wrel
    cR
    cc0
    crelexp
    co
    cid
    cR
    cuni
    cuni
    cres
    wceq
    relexp0d.2
    relexp0d.1
    cR
    cvv
    relexp0
    syl2anc
end
