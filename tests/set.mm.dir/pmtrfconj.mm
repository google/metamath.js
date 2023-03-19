include "wcel.mm"
include "wf1o.mm"
include "wa.mm"
include "cvv.mm"
include "ccom.mm"
include "ccnv.mm"
include "cid.mm"
include "cdif.mm"
include "cdm.mm"
include "c2o.mm"
include "cen.mm"
include "wbr.mm"
include "pmtrfb.mm"
include "simp1bi.mm"
include "adantr.mm"
include "simpr.mm"
include "pmtrff1o.mm"
include "f1oco.mm"
include "syl2anc.mm"
include "f1ocnv.mm"
include "adantl.mm"
include "cima.mm"
include "wf.mm"
include "wceq.mm"
include "f1of.mm"
include "syl.mm"
include "f1omvdconj.mm"
include "wf1.mm"
include "wss.mm"
include "f1of1.mm"
include "difss.mm"
include "dmss.mm"
include "ax-mp.mm"
include "fdm.mm"
include "syl5sseq.mm"
include "ssexd.mm"
include "f1imaeng.mm"
include "syl3anc.mm"
include "eqbrtrd.mm"
include "simp3bi.mm"
include "entr.mm"
include "syl3anbrc.mm"

theorem pmtrfconj
  let cD: class D
  let cR: class R
  let cT: class T
  let cF: class F
  let cG: class G
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cP: class P
  let cV: class V
  assume pmtrrn.t: |- T = ( pmTrsp ` D )
  assume pmtrrn.r: |- R = ran T


  assert |- ( ( F e. R /\ G : D -1-1-onto-> D ) -> ( ( G o. F ) o. `' G ) e. R )

  proof
    cF
    cR
    wcel
    #
    cD
    cD
    cG
    wf1o
    #
    wa
    #
    cD
    cvv
    wcel
    #
    cD
    cD
    cG
    cF
    ccom
    #
    cG
    ccnv
    #
    ccom
    #
    wf1o
    #
    @6
    cid
    cdif
    cdm
    #
    c2o
    cen
    wbr
    #
    @6
    cR
    wcel
    @0
    @3
    @1
    @0
    @3
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
    cD
    cR
    cT
    cF
    pmtrrn.t
    pmtrrn.r
    pmtrfb
    #
    simp1bi
    adantr
    #
    @2
    cD
    cD
    @4
    wf1o
    #
    cD
    cD
    @5
    wf1o
    #
    @7
    @2
    @1
    @10
    @16
    @0
    @1
    simpr
    #
    @0
    @10
    @1
    cD
    cR
    cT
    cF
    pmtrrn.t
    pmtrrn.r
    pmtrff1o
    #
    adantr
    cD
    cD
    cD
    cG
    cF
    f1oco
    syl2anc
    @1
    @17
    @0
    cD
    cD
    cG
    f1ocnv
    adantl
    cD
    cD
    cD
    @4
    @5
    f1oco
    syl2anc
    @2
    @8
    @12
    cen
    wbr
    @13
    @9
    @2
    @8
    cG
    @12
    cima
    #
    @12
    cen
    @2
    cD
    cD
    cF
    wf
    #
    @1
    @8
    @20
    wceq
    @0
    @21
    @1
    @0
    @10
    @21
    @19
    cD
    cD
    cF
    f1of
    syl
    adantr
    #
    @18
    cD
    cF
    cG
    f1omvdconj
    syl2anc
    @2
    cD
    cD
    cG
    wf1
    #
    @12
    cD
    wss
    #
    @12
    cvv
    wcel
    @20
    @12
    cen
    wbr
    @1
    @23
    @0
    cD
    cD
    cG
    f1of1
    adantl
    @2
    @21
    @24
    @22
    @21
    cF
    cdm
    #
    @12
    cD
    @11
    cF
    wss
    @12
    @25
    wss
    cF
    cid
    difss
    @11
    cF
    dmss
    ax-mp
    cD
    cD
    cF
    fdm
    syl5sseq
    syl
    #
    @2
    @12
    cD
    cvv
    @15
    @26
    ssexd
    cD
    cD
    @12
    cG
    cvv
    f1imaeng
    syl3anc
    eqbrtrd
    @0
    @13
    @1
    @0
    @3
    @10
    @13
    @14
    simp3bi
    adantr
    @8
    @12
    c2o
    entr
    syl2anc
    cD
    cR
    cT
    @6
    pmtrrn.t
    pmtrrn.r
    pmtrfb
    syl3anbrc
end
