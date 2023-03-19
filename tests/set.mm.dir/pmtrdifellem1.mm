include "wcel.mm"
include "csn.mm"
include "cdif.mm"
include "cvv.mm"
include "wf1o.mm"
include "cid.mm"
include "cdm.mm"
include "c2o.mm"
include "cen.mm"
include "wbr.mm"
include "w3a.mm"
include "cpmtr.mm"
include "cfv.mm"
include "eqid.mm"
include "pmtrfb.mm"
include "wss.mm"
include "difsnexi.mm"
include "wf.mm"
include "wceq.mm"
include "f1of.mm"
include "fdm.mm"
include "difssd.mm"
include "dmss.mm"
include "syl.mm"
include "sseq1.mm"
include "mpbird.mm"
include "sstrd.mm"
include "3syl.mm"
include "id.mm"
include "pmtrrn.mm"
include "syl5eqel.mm"
include "syl3an.mm"
include "sylbi.mm"

theorem pmtrdifellem1
  let cQ: class Q
  let cR: class R
  let cS: class S
  let cT: class T
  let cK: class K
  let cN: class N
  assume pmtrdifel.t: |- T = ran ( pmTrsp ` ( N \ { K } ) )
  assume pmtrdifel.r: |- R = ran ( pmTrsp ` N )
  assume pmtrdifel.0: |- S = ( ( pmTrsp ` N ) ` dom ( Q \ _I ) )


  assert |- ( Q e. T -> S e. R )

  proof
    cQ
    cT
    wcel
    cN
    cK
    csn
    #
    cdif
    #
    cvv
    wcel
    #
    @1
    @1
    cQ
    wf1o
    #
    cQ
    cid
    cdif
    #
    cdm
    #
    c2o
    cen
    wbr
    #
    w3a
    cS
    cR
    wcel
    #
    @1
    cT
    @1
    cpmtr
    cfv
    #
    cQ
    @8
    eqid
    pmtrdifel.t
    pmtrfb
    @2
    cN
    cvv
    wcel
    #
    @3
    @5
    cN
    wss
    #
    @6
    @6
    @7
    cK
    cN
    difsnexi
    @3
    @1
    @1
    cQ
    wf
    cQ
    cdm
    #
    @1
    wceq
    #
    @10
    @1
    @1
    cQ
    f1of
    @1
    @1
    cQ
    fdm
    @12
    @5
    @11
    cN
    @12
    @4
    cQ
    wss
    @5
    @11
    wss
    @12
    cQ
    cid
    difssd
    @4
    cQ
    dmss
    syl
    @12
    @11
    cN
    wss
    @1
    cN
    wss
    @12
    cN
    @0
    difssd
    @11
    @1
    cN
    sseq1
    mpbird
    sstrd
    3syl
    @6
    id
    @9
    @10
    @6
    w3a
    cS
    @5
    cN
    cpmtr
    cfv
    #
    cfv
    cR
    pmtrdifel.0
    cN
    @5
    cR
    @13
    cvv
    @13
    eqid
    pmtrdifel.r
    pmtrrn
    syl5eqel
    syl3an
    sylbi
end
