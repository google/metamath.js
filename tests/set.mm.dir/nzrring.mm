include "cnzr.mm"
include "wcel.mm"
include "crg.mm"
include "cur.mm"
include "cfv.mm"
include "c0g.mm"
include "wne.mm"
include "eqid.mm"
include "isnzr.mm"
include "simplbi.mm"

theorem nzrring
  let cR: class R


  assert |- ( R e. NzRing -> R e. Ring )

  proof
    cR
    cnzr
    wcel
    cR
    crg
    wcel
    cR
    cur
    cfv
    #
    cR
    c0g
    cfv
    #
    wne
    cR
    @0
    @1
    @0
    eqid
    @1
    eqid
    isnzr
    simplbi
end
