include "cdrng.mm"
include "wcel.mm"
include "crngo.mm"
include "csn.mm"
include "cdif.mm"
include "cxp.mm"
include "cres.mm"
include "cgr.mm"
include "wa.mm"
include "co.mm"
include "isdrngo1.mm"
include "wceq.mm"
include "ovres.mm"
include "adantl.mm"
include "crn.mm"
include "wi.mm"
include "eqid.mm"
include "grpocl.mm"
include "3expib.mm"
include "cdm.mm"
include "grporndm.mm"
include "wss.mm"
include "difss.mm"
include "xpss12.mm"
include "mp2an.mm"
include "wf.mm"
include "rngosm.mm"
include "fdm.mm"
include "syl.mm"
include "syl5sseqr.mm"
include "ssdmres.mm"
include "sylib.mm"
include "adantr.mm"
include "dmeqd.mm"
include "dmxpid.mm"
include "syl6eq.mm"
include "eqtrd.mm"
include "eleq2d.mm"
include "anbi12d.mm"
include "3imtr3d.mm"
include "imp.mm"
include "eqeltrrd.mm"
include "3impb.mm"
include "syl3an1b.mm"

theorem divrngcl
  let cA: class A
  let cB: class B
  let cR: class R
  let cG: class G
  let cH: class H
  let cX: class X
  let cZ: class Z
  let vg: setvar g
  let vh: setvar h
  assume isdivrng1.1: |- G = ( 1st ` R )
  assume isdivrng1.2: |- H = ( 2nd ` R )
  assume isdivrng1.3: |- Z = ( GId ` G )
  assume isdivrng1.4: |- X = ran G


  assert |- ( ( R e. DivRingOps /\ A e. ( X \ { Z } ) /\ B e. ( X \ { Z } ) ) -> ( A H B ) e. ( X \ { Z } ) )

  proof
    cR
    cdrng
    wcel
    cR
    crngo
    wcel
    #
    cH
    cX
    cZ
    csn
    #
    cdif
    #
    @2
    cxp
    #
    cres
    #
    cgr
    wcel
    #
    wa
    #
    cA
    @2
    wcel
    #
    cB
    @2
    wcel
    #
    cA
    cB
    cH
    co
    #
    @2
    wcel
    #
    cR
    cG
    cH
    cX
    cZ
    isdivrng1.1
    isdivrng1.2
    isdivrng1.3
    isdivrng1.4
    isdrngo1
    @6
    @7
    @8
    @10
    @6
    @7
    @8
    wa
    #
    wa
    cA
    cB
    @4
    co
    #
    @9
    @2
    @11
    @12
    @9
    wceq
    @6
    cA
    cB
    @2
    @2
    cH
    ovres
    adantl
    @6
    @11
    @12
    @2
    wcel
    #
    @6
    cA
    @4
    crn
    #
    wcel
    #
    cB
    @14
    wcel
    #
    wa
    #
    @12
    @14
    wcel
    #
    @11
    @13
    @5
    @17
    @18
    wi
    @0
    @5
    @15
    @16
    @18
    cA
    cB
    @4
    @14
    @14
    eqid
    grpocl
    3expib
    adantl
    @6
    @15
    @7
    @16
    @8
    @6
    @14
    @2
    cA
    @6
    @14
    @4
    cdm
    #
    cdm
    #
    @2
    @5
    @14
    @20
    wceq
    @0
    @4
    grporndm
    adantl
    @6
    @20
    @3
    cdm
    @2
    @6
    @19
    @3
    @0
    @19
    @3
    wceq
    #
    @5
    @0
    @3
    cH
    cdm
    #
    wss
    @21
    @0
    cX
    cX
    cxp
    #
    @3
    @22
    @2
    cX
    wss
    #
    @24
    @3
    @23
    wss
    cX
    @1
    difss
    #
    @25
    @2
    cX
    @2
    cX
    xpss12
    mp2an
    @0
    @23
    cX
    cH
    wf
    @22
    @23
    wceq
    cR
    cG
    cH
    cX
    isdivrng1.1
    isdivrng1.2
    isdivrng1.4
    rngosm
    @23
    cX
    cH
    fdm
    syl
    syl5sseqr
    @3
    cH
    ssdmres
    sylib
    adantr
    dmeqd
    @2
    dmxpid
    syl6eq
    eqtrd
    #
    eleq2d
    @6
    @14
    @2
    cB
    @26
    eleq2d
    anbi12d
    @6
    @14
    @2
    @12
    @26
    eleq2d
    3imtr3d
    imp
    eqeltrrd
    3impb
    syl3an1b
end
