include "cdif.mm"
include "cvv.mm"
include "neicvgbex.mm"
include "difssd.mm"
include "sselpwd.mm"

theorem neicvgrcomplex
  let wph: wff ph
  let cB: class B
  let cD: class D
  let cP: class P
  let cS: class S
  let cF: class F
  let cG: class G
  let cH: class H
  let cM: class M
  let cN: class N
  assume neicvgbex.d: |- D = ( P ` B )
  assume neicvgbex.h: |- H = ( F o. ( D o. G ) )
  assume neicvgbex.r: |- ( ph -> N H M )


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
    cG
    cH
    cM
    cN
    neicvgbex.d
    neicvgbex.h
    neicvgbex.r
    neicvgbex
    wph
    cB
    cS
    difssd
    sselpwd
end
