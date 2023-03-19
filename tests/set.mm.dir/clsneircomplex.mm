include "cdif.mm"
include "cvv.mm"
include "clsneibex.mm"
include "difssd.mm"
include "sselpwd.mm"

theorem clsneircomplex
  let wph: wff ph
  let cB: class B
  let cD: class D
  let cP: class P
  let cS: class S
  let cF: class F
  let cH: class H
  let cK: class K
  let cN: class N
  assume clsneibex.d: |- D = ( P ` B )
  assume clsneibex.h: |- H = ( F o. D )
  assume clsneibex.r: |- ( ph -> K H N )


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
    cP
    cF
    cH
    cK
    cN
    clsneibex.d
    clsneibex.h
    clsneibex.r
    clsneibex
    wph
    cB
    cS
    difssd
    sselpwd
end
