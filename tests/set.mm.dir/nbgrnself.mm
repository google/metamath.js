include "cv.mm"
include "cnbgr.mm"
include "co.mm"
include "wnel.mm"
include "wcel.mm"
include "cpr.mm"
include "wss.mm"
include "cedg.mm"
include "cfv.mm"
include "wrex.mm"
include "csn.mm"
include "cdif.mm"
include "crab.mm"
include "wa.mm"
include "wn.mm"
include "neldifsnd.mm"
include "intnanrd.mm"
include "df-nel.mm"
include "wceq.mm"
include "preq2.mm"
include "sseq1d.mm"
include "rexbidv.mm"
include "elrab.mm"
include "xchbinx.mm"
include "sylibr.mm"
include "eqidd.mm"
include "eqid.mm"
include "nbgrval.mm"
include "neleq12d.mm"
include "mpbird.mm"
include "rgen.mm"

theorem nbgrnself
  let vv: setvar v
  let cG: class G
  let cV: class V
  let ve: setvar e
  let vn: setvar n
  let cK: class K
  assume nbgrnself.v: |- V = ( Vtx ` G )

  disjoint V v
  disjoint G e
  disjoint G n
  disjoint e n
  disjoint K e
  disjoint K n
  disjoint V e
  disjoint V n
  disjoint e v
  disjoint n v
  assert |- A. v e. V v e/ ( G NeighbVtx v )

  proof
    vv
    cv
    #
    cG
    @0
    cnbgr
    co
    #
    wnel
    #
    vv
    cV
    @0
    cV
    wcel
    #
    @2
    @0
    @0
    vn
    cv
    #
    cpr
    #
    ve
    cv
    #
    wss
    #
    ve
    cG
    cedg
    cfv
    #
    wrex
    #
    vn
    cV
    @0
    csn
    cdif
    #
    crab
    #
    wnel
    #
    @3
    @0
    @10
    wcel
    #
    @0
    @0
    cpr
    #
    @6
    wss
    #
    ve
    @8
    wrex
    #
    wa
    #
    wn
    @12
    @3
    @13
    @16
    @3
    @0
    cV
    neldifsnd
    intnanrd
    @12
    @0
    @11
    wcel
    @17
    @0
    @11
    df-nel
    @9
    @16
    vn
    @0
    @10
    @4
    @0
    wceq
    #
    @7
    @15
    ve
    @8
    @18
    @5
    @14
    @6
    @4
    @0
    @0
    preq2
    sseq1d
    rexbidv
    elrab
    xchbinx
    sylibr
    @3
    @0
    @0
    @1
    @11
    @3
    @0
    eqidd
    ve
    vn
    @8
    cG
    @0
    cV
    nbgrnself.v
    @8
    eqid
    nbgrval
    neleq12d
    mpbird
    rgen
end
