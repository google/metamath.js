include "ctop.mm"
include "wcel.mm"
include "cid.mm"
include "cuni.mm"
include "cres.mm"
include "chmeo.mm"
include "co.mm"
include "chmph.mm"
include "wbr.mm"
include "ctopon.mm"
include "cfv.mm"
include "eqid.mm"
include "toptopon.mm"
include "idhmeo.mm"
include "sylbi.mm"
include "hmphi.mm"
include "syl.mm"

theorem hmphref
  let cJ: class J


  assert |- ( J e. Top -> J ~= J )

  proof
    cJ
    ctop
    wcel
    #
    cid
    cJ
    cuni
    #
    cres
    #
    cJ
    cJ
    chmeo
    co
    wcel
    #
    cJ
    cJ
    chmph
    wbr
    @0
    cJ
    @1
    ctopon
    cfv
    wcel
    @3
    cJ
    @1
    @1
    eqid
    toptopon
    cJ
    @1
    idhmeo
    sylbi
    @2
    cJ
    cJ
    hmphi
    syl
end
