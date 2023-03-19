include "cdr.mm"
include "wcel.mm"
include "cnzr.mm"
include "cbs.mm"
include "cfv.mm"
include "c0g.mm"
include "csn.mm"
include "cdif.mm"
include "crlreg.mm"
include "wss.mm"
include "cdomn.mm"
include "drngnzr.mm"
include "cui.mm"
include "crg.mm"
include "wceq.mm"
include "eqid.mm"
include "isdrng.mm"
include "simprbi.mm"
include "drngring.mm"
include "unitrrg.mm"
include "syl.mm"
include "eqsstr3d.mm"
include "isdomn2.mm"
include "sylanbrc.mm"

theorem drngdomn
  let cR: class R


  assert |- ( R e. DivRing -> R e. Domn )

  proof
    cR
    cdr
    wcel
    #
    cR
    cnzr
    wcel
    cR
    cbs
    cfv
    #
    cR
    c0g
    cfv
    #
    csn
    cdif
    #
    cR
    crlreg
    cfv
    #
    wss
    cR
    cdomn
    wcel
    cR
    drngnzr
    @0
    @3
    cR
    cui
    cfv
    #
    @4
    @0
    cR
    crg
    wcel
    #
    @5
    @3
    wceq
    @1
    cR
    @5
    @2
    @1
    eqid
    #
    @5
    eqid
    #
    @2
    eqid
    #
    isdrng
    simprbi
    @0
    @6
    @5
    @4
    wss
    cR
    drngring
    cR
    @5
    @4
    @4
    eqid
    #
    @8
    unitrrg
    syl
    eqsstr3d
    @1
    cR
    @4
    @2
    @7
    @10
    @9
    isdomn2
    sylanbrc
end
