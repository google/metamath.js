include "cdr.mm"
include "wcel.mm"
include "crg.mm"
include "clidl.mm"
include "cfv.mm"
include "clpidl.mm"
include "wss.mm"
include "clpir.mm"
include "drngring.mm"
include "c0g.mm"
include "csn.mm"
include "cbs.mm"
include "cpr.mm"
include "eqid.mm"
include "drngnidl.mm"
include "lpi0.mm"
include "lpi1.mm"
include "wa.mm"
include "snex.mm"
include "fvex.mm"
include "prss.mm"
include "bicomi.mm"
include "sylanbrc.mm"
include "syl.mm"
include "eqsstrd.mm"
include "islpir2.mm"

theorem drnglpir
  let cR: class R


  assert |- ( R e. DivRing -> R e. LPIR )

  proof
    cR
    cdr
    wcel
    #
    cR
    crg
    wcel
    #
    cR
    clidl
    cfv
    #
    cR
    clpidl
    cfv
    #
    wss
    cR
    clpir
    wcel
    cR
    drngring
    #
    @0
    @2
    cR
    c0g
    cfv
    #
    csn
    #
    cR
    cbs
    cfv
    #
    cpr
    #
    @3
    @7
    cR
    @2
    @5
    @7
    eqid
    #
    @5
    eqid
    #
    @2
    eqid
    #
    drngnidl
    @0
    @1
    @8
    @3
    wss
    #
    @4
    @1
    @6
    @3
    wcel
    #
    @7
    @3
    wcel
    #
    @12
    @3
    cR
    @5
    @3
    eqid
    #
    @10
    lpi0
    @7
    @3
    cR
    @15
    @9
    lpi1
    @13
    @14
    wa
    @12
    @6
    @7
    @3
    @5
    snex
    cR
    cbs
    fvex
    prss
    bicomi
    sylanbrc
    syl
    eqsstrd
    @3
    cR
    @2
    @15
    @11
    islpir2
    sylanbrc
end
