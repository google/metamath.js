include "cdif.mm"
include "cvv.mm"
include "ntrclsbex.mm"
include "difssd.mm"
include "sselpwd.mm"

theorem ntrclsrcomplex
  let wph: wff ph
  let cB: class B
  let cD: class D
  let cS: class S
  let cI: class I
  let cK: class K
  let cO: class O
  assume ntrclsbex.d: |- D = ( O ` B )
  assume ntrclsbex.r: |- ( ph -> I D K )


  assert |- ( ph -> ( B \ S ) e. ~P B )

  proof
    wph
    cB
    cS
    cdif
    cB
    cvv
    wph
    cB
    cD
    cI
    cK
    cO
    ntrclsbex.d
    ntrclsbex.r
    ntrclsbex
    wph
    cB
    cS
    difssd
    sselpwd
end
