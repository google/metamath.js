include "csr.mm"
include "wcel.mm"
include "cstf.mm"
include "cfv.mm"
include "coppr.mm"
include "crh.mm"
include "co.mm"
include "crg.mm"
include "eqid.mm"
include "srngrhm.mm"
include "rhmrcl1.mm"
include "syl.mm"

theorem srngring
  let cR: class R


  assert |- ( R e. *Ring -> R e. Ring )

  proof
    cR
    csr
    wcel
    cR
    cstf
    cfv
    #
    cR
    cR
    coppr
    cfv
    #
    crh
    co
    wcel
    cR
    crg
    wcel
    cR
    @0
    @1
    @1
    eqid
    @0
    eqid
    srngrhm
    cR
    @1
    @0
    rhmrcl1
    syl
end
