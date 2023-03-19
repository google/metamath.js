include "cv.mm"
include "cn0.mm"
include "wcel.mm"
include "c2ndc.mm"
include "cha.mm"
include "cehl.mm"
include "cfv.mm"
include "ctopn.mm"
include "chmph.mm"
include "cec.mm"
include "clly.mm"
include "w3a.mm"
include "wa.mm"
include "cmntop.mm"
include "df-mntop.mm"
include "relopabi.mm"

theorem relmntop
  let vj: setvar j
  let vn: setvar n


  assert |- Rel ManTop

  proof
    vn
    cv
    #
    cn0
    wcel
    vj
    cv
    #
    c2ndc
    wcel
    @1
    cha
    wcel
    @1
    @0
    cehl
    cfv
    ctopn
    cfv
    chmph
    cec
    clly
    wcel
    w3a
    wa
    vn
    vj
    cmntop
    vj
    vn
    df-mntop
    relopabi
end
