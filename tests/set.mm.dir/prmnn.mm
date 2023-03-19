include "cprime.mm"
include "wcel.mm"
include "cn.mm"
include "cv.mm"
include "cdvds.mm"
include "wbr.mm"
include "crab.mm"
include "c2o.mm"
include "cen.mm"
include "isprm.mm"
include "simplbi.mm"

theorem prmnn
  let cP: class P
  let vn: setvar n
  let vp: setvar p
  let vz: setvar z


  assert |- ( P e. Prime -> P e. NN )

  proof
    cP
    cprime
    wcel
    cP
    cn
    wcel
    vz
    cv
    cP
    cdvds
    wbr
    vz
    cn
    crab
    c2o
    cen
    wbr
    cP
    vz
    isprm
    simplbi
end
