include "wcel.mm"
include "cid.mm"
include "cdif.mm"
include "cdm.mm"
include "cpmtr.mm"
include "cfv.mm"
include "difeq1i.mm"
include "dmeqi.mm"
include "cvv.mm"
include "wss.mm"
include "c2o.mm"
include "cen.mm"
include "wbr.mm"
include "w3a.mm"
include "wceq.mm"
include "csn.mm"
include "wf1o.mm"
include "eqid.mm"
include "pmtrfb.mm"
include "difsnexi.mm"
include "wf.mm"
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
include "3anim123i.mm"
include "sylbi.mm"
include "pmtrmvd.mm"
include "syl5eq.mm"

theorem pmtrdifellem2
  let cQ: class Q
  let cR: class R
  let cS: class S
  let cT: class T
  let cK: class K
  let cN: class N
  assume pmtrdifel.t: |- T = ran ( pmTrsp ` ( N \ { K } ) )
  assume pmtrdifel.r: |- R = ran ( pmTrsp ` N )
  assume pmtrdifel.0: |- S = ( ( pmTrsp ` N ) ` dom ( Q \ _I ) )


  assert |- ( Q e. T -> dom ( S \ _I ) = dom ( Q \ _I ) )

  proof
    cQ
    cT
    wcel
    #
    cS
    cid
    cdif
    #
    cdm
    cQ
    cid
    cdif
    #
    cdm
    #
    cN
    cpmtr
    cfv
    #
    cfv
    #
    cid
    cdif
    #
    cdm
    #
    @3
    @1
    @6
    cS
    @5
    cid
    pmtrdifel.0
    difeq1i
    dmeqi
    @0
    cN
    cvv
    wcel
    #
    @3
    cN
    wss
    #
    @3
    c2o
    cen
    wbr
    #
    w3a
    #
    @7
    @3
    wceq
    @0
    cN
    cK
    csn
    #
    cdif
    #
    cvv
    wcel
    #
    @13
    @13
    cQ
    wf1o
    #
    @10
    w3a
    @11
    @13
    cT
    @13
    cpmtr
    cfv
    #
    cQ
    @16
    eqid
    pmtrdifel.t
    pmtrfb
    @14
    @8
    @15
    @9
    @10
    @10
    cK
    cN
    difsnexi
    @15
    @13
    @13
    cQ
    wf
    cQ
    cdm
    #
    @13
    wceq
    #
    @9
    @13
    @13
    cQ
    f1of
    @13
    @13
    cQ
    fdm
    @18
    @3
    @17
    cN
    @18
    @2
    cQ
    wss
    @3
    @17
    wss
    @18
    cQ
    cid
    difssd
    @2
    cQ
    dmss
    syl
    @18
    @17
    cN
    wss
    @13
    cN
    wss
    @18
    cN
    @12
    difssd
    @17
    @13
    cN
    sseq1
    mpbird
    sstrd
    3syl
    @10
    id
    3anim123i
    sylbi
    cN
    @3
    @4
    cvv
    @4
    eqid
    pmtrmvd
    syl
    syl5eq
end
