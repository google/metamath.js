include "cr.mm"
include "wcel.mm"
include "wa.mm"
include "cico.mm"
include "co.mm"
include "cv.mm"
include "cle.mm"
include "wbr.mm"
include "clt.mm"
include "crab.mm"
include "icoreval.mm"
include "cxp.mm"
include "cima.mm"
include "simpl.mm"
include "simpr.mm"
include "cxr.mm"
include "cpw.mm"
include "wf.mm"
include "wfun.mm"
include "df-ico.mm"
include "ixxf.mm"
include "ffun.mm"
include "mp1i.mm"
include "cdm.mm"
include "wss.mm"
include "rexpssxrxp.mm"
include "fdmi.mm"
include "sseqtr4i.mm"
include "a1i.mm"
include "elovimad.mm"
include "syl6eleqr.mm"
include "eqeltrrd.mm"

theorem icoreelrn
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cI: class I
  let va: setvar a
  let vb: setvar b
  assume icoreelrn.1: |- I = ( [,) " ( RR X. RR ) )

  disjoint A z
  disjoint B z
  disjoint a b
  disjoint a z
  disjoint b z
  assert |- ( ( A e. RR /\ B e. RR ) -> { z e. RR | ( A <_ z /\ z < B ) } e. I )

  proof
    cA
    cr
    wcel
    #
    cB
    cr
    wcel
    #
    wa
    #
    cA
    cB
    cico
    co
    #
    cA
    vz
    cv
    #
    cle
    wbr
    @4
    cB
    clt
    wbr
    wa
    vz
    cr
    crab
    cI
    vz
    cA
    cB
    icoreval
    @2
    @3
    cico
    cr
    cr
    cxp
    #
    cima
    cI
    @2
    cA
    cB
    cr
    cr
    cico
    @0
    @1
    simpl
    @0
    @1
    simpr
    cxr
    cxr
    cxp
    #
    cxr
    cpw
    #
    cico
    wf
    cico
    wfun
    @2
    va
    vb
    vz
    cle
    clt
    cico
    va
    vb
    vz
    df-ico
    ixxf
    #
    @6
    @7
    cico
    ffun
    mp1i
    @5
    cico
    cdm
    #
    wss
    @2
    @5
    @6
    @9
    rexpssxrxp
    @6
    @7
    cico
    @8
    fdmi
    sseqtr4i
    a1i
    elovimad
    icoreelrn.1
    syl6eleqr
    eqeltrrd
end
