include "cdr.mm"
include "wcel.mm"
include "crg.mm"
include "cur.mm"
include "cfv.mm"
include "c0g.mm"
include "wne.mm"
include "cnzr.mm"
include "drngring.mm"
include "eqid.mm"
include "drngunz.mm"
include "isnzr.mm"
include "sylanbrc.mm"

theorem drngnzr
  let cR: class R


  assert |- ( R e. DivRing -> R e. NzRing )

  proof
    cR
    cdr
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
    cnzr
    wcel
    cR
    drngring
    cR
    @0
    @1
    @1
    eqid
    #
    @0
    eqid
    #
    drngunz
    cR
    @0
    @1
    @3
    @2
    isnzr
    sylanbrc
end
