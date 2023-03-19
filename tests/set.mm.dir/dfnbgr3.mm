include "wcel.mm"
include "wfun.mm"
include "wa.mm"
include "cnbgr.mm"
include "co.mm"
include "cv.mm"
include "cpr.mm"
include "wss.mm"
include "cedg.mm"
include "cfv.mm"
include "wrex.mm"
include "csn.mm"
include "cdif.mm"
include "crab.mm"
include "cdm.mm"
include "wceq.mm"
include "eqid.mm"
include "nbgrval.mm"
include "adantr.mm"
include "crn.mm"
include "ciedg.mm"
include "edgval.mm"
include "eqcomi.mm"
include "rneqi.mm"
include "eqtri.mm"
include "rexeqi.mm"
include "wfn.mm"
include "wb.mm"
include "funfn.mm"
include "biimpi.mm"
include "adantl.mm"
include "sseq2.mm"
include "rexrn.mm"
include "syl.mm"
include "syl5bb.mm"
include "rabbidv.mm"
include "eqtrd.mm"

theorem dfnbgr3
  let vi: setvar i
  let vn: setvar n
  let cG: class G
  let cI: class I
  let cN: class N
  let cV: class V
  let ve: setvar e
  assume dfnbgr3.v: |- V = ( Vtx ` G )
  assume dfnbgr3.i: |- I = ( iEdg ` G )

  disjoint G n
  disjoint I i
  disjoint I n
  disjoint i n
  disjoint N i
  disjoint N n
  disjoint V n
  disjoint G e
  disjoint e n
  disjoint I e
  disjoint e i
  disjoint N e
  disjoint V e
  assert |- ( ( N e. V /\ Fun I ) -> ( G NeighbVtx N ) = { n e. ( V \ { N } ) | E. i e. dom I { N , n } C_ ( I ` i ) } )

  proof
    cN
    cV
    wcel
    #
    cI
    wfun
    #
    wa
    #
    cG
    cN
    cnbgr
    co
    #
    cN
    vn
    cv
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
    cN
    csn
    cdif
    #
    crab
    #
    @4
    vi
    cv
    cI
    cfv
    #
    wss
    #
    vi
    cI
    cdm
    #
    wrex
    #
    vn
    @9
    crab
    @0
    @3
    @10
    wceq
    @1
    ve
    vn
    @7
    cG
    cN
    cV
    dfnbgr3.v
    @7
    eqid
    nbgrval
    adantr
    @2
    @8
    @14
    vn
    @9
    @8
    @6
    ve
    cI
    crn
    #
    wrex
    #
    @2
    @14
    @6
    ve
    @7
    @15
    @7
    cG
    ciedg
    cfv
    #
    crn
    @15
    cG
    edgval
    @17
    cI
    cI
    @17
    dfnbgr3.i
    eqcomi
    rneqi
    eqtri
    rexeqi
    @2
    cI
    @13
    wfn
    #
    @16
    @14
    wb
    @1
    @18
    @0
    @1
    @18
    cI
    funfn
    biimpi
    adantl
    @6
    @12
    ve
    vi
    @13
    cI
    @5
    @11
    @4
    sseq2
    rexrn
    syl
    syl5bb
    rabbidv
    eqtrd
end
