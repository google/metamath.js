include "wcel.mm"
include "cpw.mm"
include "ccrd.mm"
include "cdm.mm"
include "cin.mm"
include "wf1.mm"
include "wceq.mm"
include "wa.mm"
include "cfv.mm"
include "wss.mm"
include "wpss.mm"
include "wf.mm"
include "w3a.mm"
include "f1f.mm"
include "ssid.mm"
include "canth4.mm"
include "mp3an3.mm"
include "sylan2.mm"
include "simp3d.mm"
include "wb.mm"
include "simpr.mm"
include "simp1d.mm"
include "elpw2g.mm"
include "adantr.mm"
include "mpbird.mm"
include "cv.mm"
include "wwe.mm"
include "wex.mm"
include "ccnv.mm"
include "csn.mm"
include "cima.mm"
include "wral.mm"
include "cxp.mm"
include "wbr.mm"
include "eqid.mm"
include "pm3.2i.mm"
include "cvv.mm"
include "elex.mm"
include "syl.mm"
include "ffvelrnda.mm"
include "fpwwe.mm"
include "mpbiri.mm"
include "simpld.mm"
include "fpwwelem.mm"
include "mpbid.mm"
include "simprd.mm"
include "fvex.mm"
include "weeq1.mm"
include "spcev.mm"
include "ween.mm"
include "sylibr.mm"
include "elind.mm"
include "simp2d.mm"
include "pssssd.mm"
include "sstrd.mm"
include "ssnum.mm"
include "syl2anc.mm"
include "f1fveq.mm"
include "syl12anc.mm"
include "pssned.mm"
include "necomd.mm"
include "neneqd.mm"
include "pm2.65da.mm"

theorem canthnumlem
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F
  let cV: class V
  let cW: class W
  let vr: setvar r
  let cD: class D
  assume canth4.1: |- W = { <. x , r >. | ( ( x C_ A /\ r C_ ( x X. x ) ) /\ ( r We x /\ A. y e. x ( F ` ( `' r " { y } ) ) = y ) ) }
  assume canth4.2: |- B = U. dom W
  assume canth4.3: |- C = ( `' ( W ` B ) " { ( F ` B ) } )

  disjoint r x
  disjoint r y
  disjoint A r
  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B r
  disjoint B x
  disjoint B y
  disjoint F r
  disjoint F x
  disjoint F y
  disjoint V r
  disjoint V x
  disjoint V y
  disjoint C y
  disjoint W r
  disjoint W x
  disjoint W y
  disjoint D r
  disjoint D x
  disjoint D y
  assert |- ( A e. V -> -. F : ( ~P A i^i dom card ) -1-1-> A )

  proof
    cA
    cV
    wcel
    #
    cA
    cpw
    #
    ccrd
    cdm
    #
    cin
    #
    cA
    cF
    wf1
    #
    cB
    cC
    wceq
    #
    @0
    @4
    wa
    #
    cB
    cF
    cfv
    #
    cC
    cF
    cfv
    wceq
    #
    @5
    @6
    cB
    cA
    wss
    #
    cC
    cB
    wpss
    #
    @8
    @4
    @0
    @3
    cA
    cF
    wf
    #
    @9
    @10
    @8
    w3a
    #
    @3
    cA
    cF
    f1f
    #
    @0
    @11
    @3
    @3
    wss
    @12
    @3
    ssid
    vx
    vy
    cA
    cB
    cC
    @3
    cF
    cV
    cW
    vr
    canth4.1
    canth4.2
    canth4.3
    canth4
    mp3an3
    sylan2
    #
    simp3d
    @6
    @4
    cB
    @3
    wcel
    cC
    @3
    wcel
    @8
    @5
    wb
    @0
    @4
    simpr
    #
    @6
    @1
    @2
    cB
    @6
    cB
    @1
    wcel
    #
    @9
    @6
    @9
    @10
    @8
    @14
    simp1d
    #
    @0
    @16
    @9
    wb
    @4
    cB
    cA
    cV
    elpw2g
    adantr
    mpbird
    @6
    cB
    vr
    cv
    #
    wwe
    #
    vr
    wex
    #
    cB
    @2
    wcel
    #
    @6
    cB
    cB
    cW
    cfv
    #
    wwe
    #
    @20
    @6
    @23
    @22
    ccnv
    vy
    cv
    #
    csn
    cima
    cF
    cfv
    @24
    wceq
    vy
    cB
    wral
    #
    @6
    @9
    @22
    cB
    cB
    cxp
    wss
    wa
    #
    @23
    @25
    wa
    #
    @6
    cB
    @22
    cW
    wbr
    #
    @26
    @27
    wa
    @6
    @28
    @7
    cB
    wcel
    #
    @6
    @28
    @29
    wa
    cB
    cB
    wceq
    #
    @22
    @22
    wceq
    #
    wa
    @30
    @31
    cB
    eqid
    @22
    eqid
    pm3.2i
    @6
    vx
    vy
    cA
    @22
    cF
    cW
    cB
    cB
    vr
    canth4.1
    @0
    cA
    cvv
    wcel
    @4
    cA
    cV
    elex
    adantr
    #
    @6
    @3
    cA
    vx
    cv
    cF
    @6
    @4
    @11
    @15
    @13
    syl
    ffvelrnda
    canth4.2
    fpwwe
    mpbiri
    simpld
    @6
    vx
    vy
    cA
    @22
    cF
    cW
    cB
    vr
    canth4.1
    @32
    fpwwelem
    mpbid
    simprd
    simpld
    @19
    @23
    vr
    @22
    cB
    cW
    fvex
    cB
    @18
    @22
    weeq1
    spcev
    syl
    cB
    vr
    ween
    sylibr
    #
    elind
    @6
    @1
    @2
    cC
    @6
    cC
    @1
    wcel
    #
    cC
    cA
    wss
    #
    @6
    cC
    cB
    cA
    @6
    cC
    cB
    @6
    @9
    @10
    @8
    @14
    simp2d
    #
    pssssd
    #
    @17
    sstrd
    @0
    @34
    @35
    wb
    @4
    cC
    cA
    cV
    elpw2g
    adantr
    mpbird
    @6
    @21
    cC
    cB
    wss
    cC
    @2
    wcel
    @33
    @37
    cB
    cC
    ssnum
    syl2anc
    elind
    @3
    cA
    cB
    cC
    cF
    f1fveq
    syl12anc
    mpbid
    @6
    cB
    cC
    @6
    cC
    cB
    @6
    cC
    cB
    @36
    pssned
    necomd
    neneqd
    pm2.65da
end
