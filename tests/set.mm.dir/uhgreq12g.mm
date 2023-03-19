include "wcel.mm"
include "wa.mm"
include "wceq.mm"
include "cuhgr.mm"
include "cdm.mm"
include "cpw.mm"
include "c0.mm"
include "csn.mm"
include "cdif.mm"
include "wf.mm"
include "wb.mm"
include "isuhgr.mm"
include "adantr.mm"
include "simpr.mm"
include "dmeqd.mm"
include "pweq.mm"
include "difeq1d.mm"
include "feq123d.mm"
include "adantl.mm"
include "bicomd.mm"
include "sylan9bbr.mm"
include "bitrd.mm"

theorem uhgreq12g
  let cE: class E
  let cF: class F
  let cG: class G
  let cH: class H
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  assume uhgrf.v: |- V = ( Vtx ` G )
  assume uhgrf.e: |- E = ( iEdg ` G )
  assume uhgreq12g.w: |- W = ( Vtx ` H )
  assume uhgreq12g.f: |- F = ( iEdg ` H )


  assert |- ( ( ( G e. X /\ H e. Y ) /\ ( V = W /\ E = F ) ) -> ( G e. UHGraph <-> H e. UHGraph ) )

  proof
    cG
    cX
    wcel
    #
    cH
    cY
    wcel
    #
    wa
    #
    cV
    cW
    wceq
    #
    cE
    cF
    wceq
    #
    wa
    #
    wa
    cG
    cuhgr
    wcel
    #
    cE
    cdm
    #
    cV
    cpw
    #
    c0
    csn
    #
    cdif
    #
    cE
    wf
    #
    cH
    cuhgr
    wcel
    #
    @2
    @6
    @11
    wb
    #
    @5
    @0
    @13
    @1
    cX
    cE
    cG
    cV
    uhgrf.v
    uhgrf.e
    isuhgr
    adantr
    adantr
    @5
    @11
    cF
    cdm
    #
    cW
    cpw
    #
    @9
    cdif
    #
    cF
    wf
    #
    @2
    @12
    @5
    @7
    @14
    @10
    @16
    cE
    cF
    @3
    @4
    simpr
    #
    @5
    cE
    cF
    @18
    dmeqd
    @3
    @10
    @16
    wceq
    @4
    @3
    @8
    @15
    @9
    cV
    cW
    pweq
    difeq1d
    adantr
    feq123d
    @2
    @12
    @17
    @1
    @12
    @17
    wb
    @0
    cY
    cF
    cH
    cW
    uhgreq12g.w
    uhgreq12g.f
    isuhgr
    adantl
    bicomd
    sylan9bbr
    bitrd
end
