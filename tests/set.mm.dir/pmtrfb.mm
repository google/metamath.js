include "wcel.mm"
include "cvv.mm"
include "wf1o.mm"
include "cid.mm"
include "cdif.mm"
include "cdm.mm"
include "c2o.mm"
include "cen.mm"
include "wbr.mm"
include "w3a.mm"
include "wss.mm"
include "cfv.mm"
include "wceq.mm"
include "wa.mm"
include "eqid.mm"
include "pmtrfrn.mm"
include "simpl1.mm"
include "syl.mm"
include "pmtrff1o.mm"
include "simpl3.mm"
include "3jca.mm"
include "simp2.mm"
include "difss.mm"
include "dmss.mm"
include "ax-mp.mm"
include "f1odm.mm"
include "syl5sseq.mm"
include "pmtrrn.mm"
include "syl3an2.mm"
include "simp3.mm"
include "pmtrmvd.mm"
include "f1otrspeq.mm"
include "syl22anc.mm"
include "eqeltrd.mm"
include "impbii.mm"

theorem pmtrfb
  let cD: class D
  let cR: class R
  let cT: class T
  let cF: class F
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cP: class P
  let cV: class V
  assume pmtrrn.t: |- T = ( pmTrsp ` D )
  assume pmtrrn.r: |- R = ran T


  assert |- ( F e. R <-> ( D e. _V /\ F : D -1-1-onto-> D /\ dom ( F \ _I ) ~~ 2o ) )

  proof
    cF
    cR
    wcel
    #
    cD
    cvv
    wcel
    #
    cD
    cD
    cF
    wf1o
    #
    cF
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
    #
    @0
    @1
    @2
    @5
    @0
    @1
    @4
    cD
    wss
    #
    @5
    w3a
    cF
    @4
    cT
    cfv
    #
    wceq
    #
    wa
    #
    @1
    cD
    @4
    cR
    cT
    cF
    pmtrrn.t
    pmtrrn.r
    @4
    eqid
    pmtrfrn
    #
    @1
    @7
    @5
    @9
    simpl1
    syl
    cD
    cR
    cT
    cF
    pmtrrn.t
    pmtrrn.r
    pmtrff1o
    @0
    @10
    @5
    @11
    @1
    @7
    @5
    @9
    simpl3
    syl
    3jca
    @6
    cF
    @8
    cR
    @6
    @2
    cD
    cD
    @8
    wf1o
    #
    @5
    @8
    cid
    cdif
    cdm
    @4
    wceq
    #
    @9
    @1
    @2
    @5
    simp2
    @6
    @8
    cR
    wcel
    #
    @12
    @2
    @1
    @7
    @5
    @14
    @2
    cF
    cdm
    #
    @4
    cD
    @3
    cF
    wss
    @4
    @15
    wss
    cF
    cid
    difss
    @3
    cF
    dmss
    ax-mp
    cD
    cD
    cF
    f1odm
    syl5sseq
    #
    cD
    @4
    cR
    cT
    cvv
    pmtrrn.t
    pmtrrn.r
    pmtrrn
    syl3an2
    #
    cD
    cR
    cT
    @8
    pmtrrn.t
    pmtrrn.r
    pmtrff1o
    syl
    @1
    @2
    @5
    simp3
    @2
    @1
    @7
    @5
    @13
    @16
    cD
    @4
    cT
    cvv
    pmtrrn.t
    pmtrmvd
    syl3an2
    cD
    cF
    @8
    f1otrspeq
    syl22anc
    @17
    eqeltrd
    impbii
end
