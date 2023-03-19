include "wcel.mm"
include "wss.mm"
include "c2o.mm"
include "cen.mm"
include "wbr.mm"
include "w3a.mm"
include "cfv.mm"
include "cid.mm"
include "cdif.mm"
include "cdm.mm"
include "cv.mm"
include "wne.mm"
include "crab.mm"
include "cin.mm"
include "wf.mm"
include "wfn.mm"
include "wceq.mm"
include "pmtrf.mm"
include "ffn.mm"
include "fndifnfp.mm"
include "3syl.mm"
include "wa.mm"
include "csn.mm"
include "cuni.mm"
include "cif.mm"
include "pmtrfv.mm"
include "neeq1d.mm"
include "wb.mm"
include "iffalse.mm"
include "necon1ai.mm"
include "iftrue.mm"
include "adantl.mm"
include "c1o.mm"
include "com.mm"
include "csuc.mm"
include "1onn.mm"
include "a1i.mm"
include "simpl3.mm"
include "df-2o.mm"
include "syl6breq.mm"
include "simpr.mm"
include "dif1en.mm"
include "syl3anc.mm"
include "en1uniel.mm"
include "eldifsni.mm"
include "eqnetrd.mm"
include "ex.mm"
include "impbid2.mm"
include "adantr.mm"
include "bitrd.mm"
include "rabbidva.mm"
include "incom.mm"
include "dfin5.mm"
include "eqtri.mm"
include "syl6eqr.mm"
include "simp2.mm"
include "df-ss.mm"
include "sylib.mm"
include "3eqtrd.mm"

theorem pmtrmvd
  let cD: class D
  let cP: class P
  let cT: class T
  let cV: class V
  let vd: setvar d
  let vp: setvar p
  let vy: setvar y
  let vz: setvar z
  let cZ: class Z
  assume pmtrfval.t: |- T = ( pmTrsp ` D )


  assert |- ( ( D e. V /\ P C_ D /\ P ~~ 2o ) -> dom ( ( T ` P ) \ _I ) = P )

  proof
    cD
    cV
    wcel
    #
    cP
    cD
    wss
    #
    cP
    c2o
    cen
    wbr
    #
    w3a
    #
    cP
    cT
    cfv
    #
    cid
    cdif
    cdm
    #
    vz
    cv
    #
    @4
    cfv
    #
    @6
    wne
    #
    vz
    cD
    crab
    #
    cP
    cD
    cin
    #
    cP
    @3
    cD
    cD
    @4
    wf
    @4
    cD
    wfn
    @5
    @9
    wceq
    cD
    cP
    cT
    cV
    pmtrfval.t
    pmtrf
    cD
    cD
    @4
    ffn
    vz
    cD
    @4
    fndifnfp
    3syl
    @3
    @9
    @6
    cP
    wcel
    #
    vz
    cD
    crab
    #
    @10
    @3
    @8
    @11
    vz
    cD
    @3
    @6
    cD
    wcel
    #
    wa
    #
    @8
    @11
    cP
    @6
    csn
    cdif
    #
    cuni
    #
    @6
    cif
    #
    @6
    wne
    #
    @11
    @14
    @7
    @17
    @6
    cD
    cP
    cT
    cV
    @6
    pmtrfval.t
    pmtrfv
    neeq1d
    @3
    @18
    @11
    wb
    @13
    @3
    @18
    @11
    @11
    @17
    @6
    @11
    @16
    @6
    iffalse
    necon1ai
    @3
    @11
    @18
    @3
    @11
    wa
    #
    @17
    @16
    @6
    @11
    @17
    @16
    wceq
    @3
    @11
    @16
    @6
    iftrue
    adantl
    @19
    @15
    c1o
    cen
    wbr
    #
    @16
    @15
    wcel
    @16
    @6
    wne
    @19
    c1o
    com
    wcel
    #
    cP
    c1o
    csuc
    #
    cen
    wbr
    @11
    @20
    @21
    @19
    1onn
    a1i
    @19
    cP
    c2o
    @22
    cen
    @0
    @1
    @2
    @11
    simpl3
    df-2o
    syl6breq
    @3
    @11
    simpr
    cP
    c1o
    @6
    dif1en
    syl3anc
    @15
    en1uniel
    @16
    cP
    @6
    eldifsni
    3syl
    eqnetrd
    ex
    impbid2
    adantr
    bitrd
    rabbidva
    @10
    cD
    cP
    cin
    @12
    cP
    cD
    incom
    vz
    cD
    cP
    dfin5
    eqtri
    syl6eqr
    @3
    @1
    @10
    cP
    wceq
    @0
    @1
    @2
    simp2
    cP
    cD
    df-ss
    sylib
    3eqtrd
end
