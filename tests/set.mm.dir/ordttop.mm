include "wcel.mm"
include "cordt.mm"
include "cfv.mm"
include "cdm.mm"
include "ctopon.mm"
include "ctop.mm"
include "eqid.mm"
include "ordttopon.mm"
include "topontop.mm"
include "syl.mm"

theorem ordttop
  let cR: class R
  let cV: class V


  assert |- ( R e. V -> ( ordTop ` R ) e. Top )

  proof
    cR
    cV
    wcel
    cR
    cordt
    cfv
    #
    cR
    cdm
    #
    ctopon
    cfv
    wcel
    @0
    ctop
    wcel
    cR
    cV
    @1
    @1
    eqid
    ordttopon
    @1
    @0
    topontop
    syl
end
