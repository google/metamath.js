include "cn0.mm"
include "wcel.mm"
include "wa.mm"
include "cmntop.mm"
include "wbr.mm"
include "c2ndc.mm"
include "cha.mm"
include "cehl.mm"
include "cfv.mm"
include "ctopn.mm"
include "chmph.mm"
include "cec.mm"
include "clly.mm"
include "w3a.mm"
include "cv.mm"
include "wceq.mm"
include "simpl.mm"
include "eleq1d.mm"
include "simpr.mm"
include "fveq2.mm"
include "fveq2d.mm"
include "eceq1d.mm"
include "llyeq.mm"
include "syl.mm"
include "adantr.mm"
include "eleq12d.mm"
include "3anbi123d.mm"
include "anbi12d.mm"
include "df-mntop.mm"
include "brabga.mm"
include "biantrurd.mm"
include "bitr4d.mm"

theorem ismntoplly
  let cJ: class J
  let cN: class N
  let cV: class V
  let vj: setvar j
  let vn: setvar n
  let vu: setvar u
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( N e. NN0 /\ J e. V ) -> ( N ManTop J <-> ( J e. 2ndc /\ J e. Haus /\ J e. Locally [ ( TopOpen ` ( EEhil ` N ) ) ] ~= ) ) )

  proof
    cN
    cn0
    wcel
    #
    cJ
    cV
    wcel
    #
    wa
    #
    cN
    cJ
    cmntop
    wbr
    @0
    cJ
    c2ndc
    wcel
    #
    cJ
    cha
    wcel
    #
    cJ
    cN
    cehl
    cfv
    #
    ctopn
    cfv
    #
    chmph
    cec
    #
    clly
    #
    wcel
    #
    w3a
    #
    wa
    #
    @10
    vn
    cv
    #
    cn0
    wcel
    #
    vj
    cv
    #
    c2ndc
    wcel
    #
    @14
    cha
    wcel
    #
    @14
    @12
    cehl
    cfv
    #
    ctopn
    cfv
    #
    chmph
    cec
    #
    clly
    #
    wcel
    #
    w3a
    #
    wa
    @11
    vn
    vj
    cN
    cJ
    cmntop
    cn0
    cV
    @12
    cN
    wceq
    #
    @14
    cJ
    wceq
    #
    wa
    #
    @13
    @0
    @22
    @10
    @25
    @12
    cN
    cn0
    @23
    @24
    simpl
    eleq1d
    @25
    @15
    @3
    @16
    @4
    @21
    @9
    @25
    @14
    cJ
    c2ndc
    @23
    @24
    simpr
    #
    eleq1d
    @25
    @14
    cJ
    cha
    @26
    eleq1d
    @25
    @14
    cJ
    @20
    @8
    @26
    @23
    @20
    @8
    wceq
    #
    @24
    @23
    @19
    @7
    wceq
    @27
    @23
    @18
    @6
    chmph
    @23
    @17
    @5
    ctopn
    @12
    cN
    cehl
    fveq2
    fveq2d
    eceq1d
    @19
    @7
    llyeq
    syl
    adantr
    eleq12d
    3anbi123d
    anbi12d
    vj
    vn
    df-mntop
    brabga
    @2
    @0
    @10
    @0
    @1
    simpl
    biantrurd
    bitr4d
end
