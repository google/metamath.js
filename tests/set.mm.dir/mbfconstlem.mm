include "cvol.mm"
include "cdm.mm"
include "wcel.mm"
include "cr.mm"
include "wa.mm"
include "csn.mm"
include "cxp.mm"
include "ccnv.mm"
include "cima.mm"
include "wss.mm"
include "cnvimass.mm"
include "a1i.mm"
include "crn.mm"
include "cnvimarndm.mm"
include "wf.mm"
include "fconst6g.mm"
include "adantl.mm"
include "frn.mm"
include "imass2.mm"
include "3syl.mm"
include "syl5eqssr.mm"
include "eqssd.mm"
include "wceq.mm"
include "fconstg.mm"
include "ad2antlr.mm"
include "fdm.mm"
include "syl.mm"
include "eqtrd.mm"
include "simpll.mm"
include "eqeltrd.mm"
include "wn.mm"
include "c0.mm"
include "cin.mm"
include "incom.mm"
include "simpr.mm"
include "disjsn.mm"
include "sylibr.mm"
include "syl5eq.mm"
include "fimacnvdisj.mm"
include "syl2anc.mm"
include "0mbl.mm"
include "syl6eqel.mm"
include "pm2.61dan.mm"

theorem mbfconstlem
  let cA: class A
  let cB: class B
  let cC: class C
  let vf: setvar f
  let vx: setvar x
  let vy: setvar y
  let cF: class F
  let vz: setvar z


  assert |- ( ( A e. dom vol /\ C e. RR ) -> ( `' ( A X. { C } ) " B ) e. dom vol )

  proof
    cA
    cvol
    cdm
    #
    wcel
    #
    cC
    cr
    wcel
    #
    wa
    #
    cC
    cB
    wcel
    #
    cA
    cC
    csn
    #
    cxp
    #
    ccnv
    #
    cB
    cima
    #
    @0
    wcel
    @3
    @4
    wa
    #
    @8
    cA
    @0
    @9
    @8
    @6
    cdm
    #
    cA
    @9
    @8
    @10
    @8
    @10
    wss
    @9
    @6
    cB
    cnvimass
    a1i
    @9
    @10
    @7
    @6
    crn
    #
    cima
    #
    @8
    @6
    cnvimarndm
    @9
    cA
    cB
    @6
    wf
    #
    @11
    cB
    wss
    @12
    @8
    wss
    @4
    @13
    @3
    cA
    cC
    cB
    fconst6g
    adantl
    cA
    cB
    @6
    frn
    @11
    cB
    @7
    imass2
    3syl
    syl5eqssr
    eqssd
    @9
    cA
    @5
    @6
    wf
    #
    @10
    cA
    wceq
    @2
    @14
    @1
    @4
    cA
    cC
    cr
    fconstg
    #
    ad2antlr
    cA
    @5
    @6
    fdm
    syl
    eqtrd
    @1
    @2
    @4
    simpll
    eqeltrd
    @3
    @4
    wn
    #
    wa
    #
    @8
    c0
    @0
    @17
    @14
    @5
    cB
    cin
    #
    c0
    wceq
    @8
    c0
    wceq
    @2
    @14
    @1
    @16
    @15
    ad2antlr
    @17
    @18
    cB
    @5
    cin
    #
    c0
    @5
    cB
    incom
    @17
    @16
    @19
    c0
    wceq
    @3
    @16
    simpr
    cB
    cC
    disjsn
    sylibr
    syl5eq
    cA
    @5
    cB
    @6
    fimacnvdisj
    syl2anc
    0mbl
    syl6eqel
    pm2.61dan
end
