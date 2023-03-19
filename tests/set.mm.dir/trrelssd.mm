include "ccom.mm"
include "coss12d.mm"
include "sstrd.mm"

theorem trrelssd
  let wph: wff ph
  let cR: class R
  let cS: class S
  let cT: class T
  assume trrelssd.r: |- ( ph -> ( R o. R ) C_ R )
  assume trrelssd.s: |- ( ph -> S C_ R )
  assume trrelssd.t: |- ( ph -> T C_ R )


  assert |- ( ph -> ( S o. T ) C_ R )

  proof
    wph
    cS
    cT
    ccom
    cR
    cR
    ccom
    cR
    wph
    cS
    cR
    cT
    cR
    trrelssd.s
    trrelssd.t
    coss12d
    trrelssd.r
    sstrd
end
