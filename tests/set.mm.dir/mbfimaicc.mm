include "cmbf.mm"
include "wcel.mm"
include "cr.mm"
include "wf.mm"
include "wa.mm"
include "ccnv.mm"
include "cicc.mm"
include "co.mm"
include "cima.mm"
include "cmnf.mm"
include "cioo.mm"
include "cpnf.mm"
include "cun.mm"
include "cdif.mm"
include "cvol.mm"
include "cdm.mm"
include "wss.mm"
include "wceq.mm"
include "iccssre.mm"
include "adantl.mm"
include "dfss4.mm"
include "sylib.mm"
include "difreicc.mm"
include "difeq2d.mm"
include "eqtr3d.mm"
include "imaeq2d.mm"
include "wfun.mm"
include "ffun.mm"
include "funcnvcnv.mm"
include "syl.mm"
include "ad2antlr.mm"
include "imadif.mm"
include "eqtrd.mm"
include "fimacnv.mm"
include "mbfdm.mm"
include "fdm.mm"
include "eleq1d.mm"
include "biimpac.mm"
include "sylan.mm"
include "eqeltrd.mm"
include "imaundi.mm"
include "mbfima.mm"
include "unmbl.mm"
include "syl2anc.mm"
include "syl5eqel.mm"
include "difmbl.mm"
include "adantr.mm"

theorem mbfimaicc
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F
  let vf: setvar f
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( ( ( F e. MblFn /\ F : A --> RR ) /\ ( B e. RR /\ C e. RR ) ) -> ( `' F " ( B [,] C ) ) e. dom vol )

  proof
    cF
    cmbf
    wcel
    #
    cA
    cr
    cF
    wf
    #
    wa
    #
    cB
    cr
    wcel
    cC
    cr
    wcel
    wa
    #
    wa
    #
    cF
    ccnv
    #
    cB
    cC
    cicc
    co
    #
    cima
    #
    @5
    cr
    cima
    #
    @5
    cmnf
    cB
    cioo
    co
    #
    cC
    cpnf
    cioo
    co
    #
    cun
    #
    cima
    #
    cdif
    #
    cvol
    cdm
    #
    @4
    @7
    @5
    cr
    @11
    cdif
    #
    cima
    #
    @13
    @4
    @6
    @15
    @5
    @4
    cr
    cr
    @6
    cdif
    #
    cdif
    #
    @6
    @15
    @4
    @6
    cr
    wss
    #
    @18
    @6
    wceq
    @3
    @19
    @2
    cB
    cC
    iccssre
    adantl
    @6
    cr
    dfss4
    sylib
    @4
    @17
    @11
    cr
    @3
    @17
    @11
    wceq
    @2
    cB
    cC
    difreicc
    adantl
    difeq2d
    eqtr3d
    imaeq2d
    @4
    @5
    ccnv
    wfun
    #
    @16
    @13
    wceq
    @1
    @20
    @0
    @3
    @1
    cF
    wfun
    @20
    cA
    cr
    cF
    ffun
    cF
    funcnvcnv
    syl
    ad2antlr
    cr
    @11
    @5
    imadif
    syl
    eqtrd
    @2
    @13
    @14
    wcel
    #
    @3
    @2
    @8
    @14
    wcel
    @12
    @14
    wcel
    @21
    @2
    @8
    cA
    @14
    @1
    @8
    cA
    wceq
    @0
    cA
    cr
    cF
    fimacnv
    adantl
    @0
    cF
    cdm
    #
    @14
    wcel
    #
    @1
    cA
    @14
    wcel
    #
    cF
    mbfdm
    @1
    @23
    @24
    @1
    @22
    cA
    @14
    cA
    cr
    cF
    fdm
    eleq1d
    biimpac
    sylan
    eqeltrd
    @2
    @12
    @5
    @9
    cima
    #
    @5
    @10
    cima
    #
    cun
    #
    @14
    @5
    @9
    @10
    imaundi
    @2
    @25
    @14
    wcel
    @26
    @14
    wcel
    @27
    @14
    wcel
    cA
    cmnf
    cB
    cF
    mbfima
    cA
    cC
    cpnf
    cF
    mbfima
    @25
    @26
    unmbl
    syl2anc
    syl5eqel
    @8
    @12
    difmbl
    syl2anc
    adantr
    eqeltrd
end
