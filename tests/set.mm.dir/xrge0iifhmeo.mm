include "cle.mm"
include "cc0.mm"
include "c1.mm"
include "cicc.mm"
include "co.mm"
include "cxp.mm"
include "cin.mm"
include "cordt.mm"
include "cfv.mm"
include "ccnv.mm"
include "cpnf.mm"
include "chmeo.mm"
include "cii.mm"
include "cvv.mm"
include "wcel.mm"
include "wiso.mm"
include "cps.mm"
include "ctsr.mm"
include "letsr.mm"
include "tsrps.mm"
include "ax-mp.mm"
include "elexi.mm"
include "inex1.mm"
include "cnvps.mm"
include "clt.mm"
include "xrge0iifiso.mm"
include "cxr.mm"
include "wss.mm"
include "wb.mm"
include "iccssxr.mm"
include "gtiso.mm"
include "mp2an.mm"
include "mpbi.mm"
include "isores1.mm"
include "isores2.mm"
include "cdm.mm"
include "wceq.mm"
include "ledm.mm"
include "psssdm.mm"
include "eqcomi.mm"
include "crn.mm"
include "lern.mm"
include "df-rn.mm"
include "eqtri.mm"
include "ordthmeo.mm"
include "mp3an.mm"
include "dfii5.mm"
include "crest.mm"
include "cv.mm"
include "iccss2.mm"
include "cnvordtrestixx.mm"
include "oveq12i.mm"
include "eleqtrri.mm"

theorem xrge0iifhmeo
  let vx: setvar x
  let cF: class F
  let cJ: class J
  let vy: setvar y
  let cX: class X
  let vw: setvar w
  let vz: setvar z
  let vu: setvar u
  assume xrge0iifhmeo.1: |- F = ( x e. ( 0 [,] 1 ) |-> if ( x = 0 , +oo , -u ( log ` x ) ) )
  assume xrge0iifhmeo.k: |- J = ( ( ordTop ` <_ ) |`t ( 0 [,] +oo ) )

  disjoint F x
  disjoint x y
  disjoint X x
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint F w
  disjoint x z
  disjoint y z
  disjoint F y
  disjoint F z
  disjoint u x
  assert |- F e. ( II Homeo J )

  proof
    cF
    cle
    cc0
    c1
    cicc
    co
    #
    @0
    cxp
    #
    cin
    #
    cordt
    cfv
    #
    cle
    ccnv
    #
    cc0
    cpnf
    cicc
    co
    #
    @5
    cxp
    #
    cin
    #
    cordt
    cfv
    #
    chmeo
    co
    #
    cii
    cJ
    chmeo
    co
    @2
    cvv
    wcel
    @7
    cvv
    wcel
    @0
    @5
    @2
    @7
    cF
    wiso
    #
    cF
    @9
    wcel
    cle
    @1
    cle
    cps
    cle
    ctsr
    wcel
    cle
    cps
    wcel
    #
    letsr
    cle
    tsrps
    ax-mp
    #
    elexi
    inex1
    @4
    @6
    @4
    cps
    @11
    @4
    cps
    wcel
    #
    @12
    cle
    cnvps
    ax-mp
    #
    elexi
    inex1
    @0
    @5
    @2
    @4
    cF
    wiso
    #
    @10
    @0
    @5
    cle
    @4
    cF
    wiso
    #
    @15
    @0
    @5
    clt
    clt
    ccnv
    cF
    wiso
    #
    @16
    vx
    cF
    xrge0iifhmeo.1
    xrge0iifiso
    @0
    cxr
    wss
    #
    @5
    cxr
    wss
    #
    @17
    @16
    wb
    cc0
    c1
    iccssxr
    #
    cc0
    cpnf
    iccssxr
    #
    @0
    @5
    cF
    gtiso
    mp2an
    mpbi
    @0
    @5
    cle
    @4
    cF
    isores1
    mpbi
    @0
    @5
    @2
    @4
    cF
    isores2
    mpbi
    @2
    @7
    cF
    cvv
    cvv
    @0
    @5
    @2
    cdm
    #
    @0
    @11
    @18
    @22
    @0
    wceq
    @12
    @20
    @0
    cle
    cxr
    ledm
    psssdm
    mp2an
    eqcomi
    @7
    cdm
    #
    @5
    @13
    @19
    @23
    @5
    wceq
    @14
    @21
    @5
    @4
    cxr
    cxr
    cle
    crn
    @4
    cdm
    lern
    cle
    df-rn
    eqtri
    psssdm
    mp2an
    eqcomi
    ordthmeo
    mp3an
    cii
    @3
    cJ
    @8
    chmeo
    dfii5
    cJ
    cle
    cordt
    cfv
    @5
    crest
    co
    @8
    xrge0iifhmeo.k
    vx
    vy
    @5
    @21
    cc0
    cpnf
    vx
    cv
    vy
    cv
    iccss2
    cnvordtrestixx
    eqtri
    oveq12i
    eleqtrri
end
