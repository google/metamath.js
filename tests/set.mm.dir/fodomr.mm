include "c0.mm"
include "csdm.mm"
include "wbr.mm"
include "cdom.mm"
include "wa.mm"
include "cvv.mm"
include "wcel.mm"
include "cv.mm"
include "wex.mm"
include "wf1.mm"
include "wfo.mm"
include "reldom.mm"
include "brrelex2i.mm"
include "adantl.mm"
include "wb.mm"
include "brrelexi.mm"
include "wne.mm"
include "0sdomg.mm"
include "n0.mm"
include "syl6bb.mm"
include "syl.mm"
include "biimpac.mm"
include "brdomi.mm"
include "wi.mm"
include "ccnv.mm"
include "crn.mm"
include "cdif.mm"
include "csn.mm"
include "cxp.mm"
include "cun.mm"
include "difexg.mm"
include "snex.mm"
include "xpexg.mm"
include "sylancl.mm"
include "vex.mm"
include "cnvex.mm"
include "jctil.mm"
include "unexb.mm"
include "sylib.mm"
include "wfn.mm"
include "wceq.mm"
include "wfun.mm"
include "cdm.mm"
include "cin.mm"
include "wf.mm"
include "df-f1.mm"
include "simprbi.mm"
include "fconst.mm"
include "ffun.mm"
include "ax-mp.mm"
include "jctir.mm"
include "df-rn.mm"
include "eqcomi.mm"
include "snnz.mm"
include "dmxp.mm"
include "ineq12i.mm"
include "disjdif.mm"
include "eqtri.mm"
include "funun.mm"
include "dmun.mm"
include "uneq1i.mm"
include "uneq2i.mm"
include "3eqtr2i.mm"
include "wss.mm"
include "f1f.mm"
include "frn.mm"
include "undif.mm"
include "syl5eq.mm"
include "df-fn.mm"
include "sylanbrc.mm"
include "rnun.mm"
include "dfdm4.mm"
include "f1dm.mm"
include "syl5eqr.mm"
include "uneq1d.mm"
include "xpeq1.mm"
include "0xp.mm"
include "syl6eq.mm"
include "rneqd.mm"
include "rn0.mm"
include "0ss.mm"
include "syl6eqss.mm"
include "a1d.mm"
include "rnxp.mm"
include "adantr.mm"
include "snssi.mm"
include "eqsstrd.mm"
include "ex.mm"
include "pm2.61ine.mm"
include "ssequn2.mm"
include "sylan9eqr.mm"
include "df-fo.mm"
include "foeq1.mm"
include "spcegv.mm"
include "syl2im.mm"
include "expdimp.mm"
include "exlimdv.mm"
include "syl3c.mm"

theorem fodomr
  let cA: class A
  let cB: class B
  let vf: setvar f
  let vg: setvar g
  let vz: setvar z
  let cC: class C

  disjoint A f
  disjoint B f
  disjoint f g
  disjoint f z
  disjoint g z
  disjoint A g
  disjoint A z
  disjoint B g
  disjoint B z
  disjoint C z
  assert |- ( ( (/) ~< B /\ B ~<_ A ) -> E. f f : A -onto-> B )

  proof
    c0
    cB
    csdm
    wbr
    #
    cB
    cA
    cdom
    wbr
    #
    wa
    cA
    cvv
    wcel
    #
    vz
    cv
    #
    cB
    wcel
    #
    vz
    wex
    #
    cB
    cA
    vg
    cv
    #
    wf1
    #
    vg
    wex
    #
    cA
    cB
    vf
    cv
    #
    wfo
    #
    vf
    wex
    #
    @1
    @2
    @0
    cB
    cA
    cdom
    reldom
    brrelex2i
    adantl
    @1
    @0
    @5
    @1
    cB
    cvv
    wcel
    #
    @0
    @5
    wb
    cB
    cA
    cdom
    reldom
    brrelexi
    @12
    @0
    cB
    c0
    wne
    @5
    cB
    cvv
    0sdomg
    vz
    cB
    n0
    syl6bb
    syl
    biimpac
    @1
    @8
    @0
    cB
    cA
    vg
    brdomi
    adantl
    @2
    @4
    @8
    @11
    wi
    #
    vz
    @2
    @4
    @13
    @2
    @4
    wa
    @7
    @11
    vg
    @2
    @4
    @7
    @11
    @2
    @6
    ccnv
    #
    cA
    @6
    crn
    #
    cdif
    #
    @3
    csn
    #
    cxp
    #
    cun
    #
    cvv
    wcel
    #
    @4
    @7
    wa
    #
    cA
    cB
    @19
    wfo
    #
    @11
    @2
    @14
    cvv
    wcel
    #
    @18
    cvv
    wcel
    #
    wa
    @20
    @2
    @24
    @23
    @2
    @16
    cvv
    wcel
    @17
    cvv
    wcel
    @24
    cA
    @15
    cvv
    difexg
    @3
    snex
    @16
    @17
    cvv
    cvv
    xpexg
    sylancl
    @6
    vg
    vex
    cnvex
    jctil
    @14
    @18
    unexb
    sylib
    @21
    @19
    cA
    wfn
    #
    @19
    crn
    #
    cB
    wceq
    @22
    @21
    @19
    wfun
    #
    @19
    cdm
    #
    cA
    wceq
    #
    @25
    @7
    @27
    @4
    @7
    @14
    wfun
    #
    @18
    wfun
    #
    wa
    @14
    cdm
    #
    @18
    cdm
    #
    cin
    #
    c0
    wceq
    @27
    @7
    @30
    @31
    @7
    cB
    cA
    @6
    wf
    #
    @30
    cB
    cA
    @6
    df-f1
    simprbi
    @16
    @17
    @18
    wf
    @31
    @16
    @3
    vz
    vex
    #
    fconst
    @16
    @17
    @18
    ffun
    ax-mp
    jctir
    @34
    @15
    @16
    cin
    c0
    @32
    @15
    @33
    @16
    @15
    @32
    @6
    df-rn
    #
    eqcomi
    @17
    c0
    wne
    @33
    @16
    wceq
    @3
    @36
    snnz
    @16
    @17
    dmxp
    ax-mp
    #
    ineq12i
    @15
    cA
    disjdif
    eqtri
    @14
    @18
    funun
    sylancl
    adantl
    @7
    @29
    @4
    @7
    @28
    @15
    @16
    cun
    #
    cA
    @28
    @32
    @33
    cun
    @15
    @33
    cun
    @39
    @14
    @18
    dmun
    @15
    @32
    @33
    @37
    uneq1i
    @33
    @16
    @15
    @38
    uneq2i
    3eqtr2i
    @7
    @15
    cA
    wss
    #
    @39
    cA
    wceq
    @7
    @35
    @40
    cB
    cA
    @6
    f1f
    cB
    cA
    @6
    frn
    syl
    @15
    cA
    undif
    sylib
    syl5eq
    adantl
    @19
    cA
    df-fn
    sylanbrc
    @21
    @26
    @14
    crn
    #
    @18
    crn
    #
    cun
    #
    cB
    @14
    @18
    rnun
    @7
    @4
    @43
    cB
    @42
    cun
    #
    cB
    @7
    @41
    cB
    @42
    @7
    @41
    @6
    cdm
    cB
    @6
    dfdm4
    cB
    cA
    @6
    f1dm
    syl5eqr
    uneq1d
    @4
    @42
    cB
    wss
    #
    @44
    cB
    wceq
    @4
    @45
    wi
    @16
    c0
    @16
    c0
    wceq
    #
    @45
    @4
    @46
    @42
    c0
    cB
    @46
    @42
    c0
    crn
    c0
    @46
    @18
    c0
    @46
    @18
    c0
    @17
    cxp
    c0
    @16
    c0
    @17
    xpeq1
    @17
    0xp
    syl6eq
    rneqd
    rn0
    syl6eq
    cB
    0ss
    syl6eqss
    a1d
    @16
    c0
    wne
    #
    @4
    @45
    @47
    @4
    wa
    @42
    @17
    cB
    @47
    @42
    @17
    wceq
    @4
    @16
    @17
    rnxp
    adantr
    @4
    @17
    cB
    wss
    @47
    @3
    cB
    snssi
    adantl
    eqsstrd
    ex
    pm2.61ine
    @42
    cB
    ssequn2
    sylib
    sylan9eqr
    syl5eq
    cA
    cB
    @19
    df-fo
    sylanbrc
    @10
    @22
    vf
    @19
    cvv
    cA
    cB
    @9
    @19
    foeq1
    spcegv
    syl2im
    expdimp
    exlimdv
    ex
    exlimdv
    syl3c
end
