include "wcel.mm"
include "cmagm.mm"
include "cv.mm"
include "cdm.mm"
include "wceq.mm"
include "cxp.mm"
include "wf.mm"
include "wa.mm"
include "wex.mm"
include "feq1.mm"
include "exbidv.mm"
include "df-mgmOLD.mm"
include "elab2g.mm"
include "c0.mm"
include "wi.mm"
include "f00.mm"
include "dmeq.mm"
include "dm0.mm"
include "dmeqi.mm"
include "eqtri.mm"
include "syl6req.mm"
include "syl.mm"
include "adantr.mm"
include "sylbi.mm"
include "wb.mm"
include "xpeq12.mm"
include "anidms.mm"
include "feq23.mm"
include "mpancom.mm"
include "eqeq1.mm"
include "imbi12d.mm"
include "mpbiri.mm"
include "wn.mm"
include "fdm.mm"
include "wne.mm"
include "df-ne.mm"
include "dmxp.mm"
include "sylbir.mm"
include "eqeq1d.mm"
include "biimpcd.mm"
include "eqcoms.mm"
include "3syl.mm"
include "com12.mm"
include "pm2.61i.mm"
include "pm4.71ri.mm"
include "exbii.mm"
include "syl6bb.mm"
include "cvv.mm"
include "dmexg.mm"
include "eqcomi.mm"
include "xpeq12i.mm"
include "feq23i.mm"
include "ceqsexgv.mm"
include "bitrd.mm"

theorem ismgmOLD
  let cA: class A
  let cG: class G
  let cX: class X
  let vg: setvar g
  let vt: setvar t
  assume ismgmOLD.1: |- X = dom dom G


  assert |- ( G e. A -> ( G e. Magma <-> G : ( X X. X ) --> X ) )

  proof
    cG
    cA
    wcel
    #
    cG
    cmagm
    wcel
    #
    vt
    cv
    #
    cG
    cdm
    #
    cdm
    #
    wceq
    #
    @2
    @2
    cxp
    #
    @2
    cG
    wf
    #
    wa
    #
    vt
    wex
    #
    cX
    cX
    cxp
    #
    cX
    cG
    wf
    #
    @0
    @1
    @7
    vt
    wex
    #
    @9
    @6
    @2
    vg
    cv
    #
    wf
    #
    vt
    wex
    @12
    vg
    cG
    cmagm
    cA
    @13
    cG
    wceq
    @14
    @7
    vt
    @6
    @2
    @13
    cG
    feq1
    exbidv
    vt
    vg
    df-mgmOLD
    elab2g
    @7
    @8
    vt
    @7
    @5
    @2
    c0
    wceq
    #
    @7
    @5
    wi
    #
    @15
    @16
    c0
    c0
    cxp
    #
    c0
    cG
    wf
    #
    c0
    @4
    wceq
    #
    wi
    @18
    cG
    c0
    wceq
    #
    @17
    c0
    wceq
    #
    wa
    @19
    @17
    cG
    f00
    @20
    @19
    @21
    @20
    @3
    c0
    cdm
    #
    wceq
    #
    @19
    cG
    c0
    dmeq
    @23
    @4
    @22
    cdm
    #
    c0
    @3
    @22
    dmeq
    @24
    @22
    c0
    @22
    c0
    dm0
    dmeqi
    dm0
    eqtri
    syl6req
    syl
    adantr
    sylbi
    @15
    @7
    @18
    @5
    @19
    @6
    @17
    wceq
    #
    @15
    @7
    @18
    wb
    @15
    @25
    @2
    c0
    @2
    c0
    xpeq12
    anidms
    @6
    @2
    @17
    c0
    cG
    feq23
    mpancom
    @2
    c0
    @4
    eqeq1
    imbi12d
    mpbiri
    @7
    @15
    wn
    #
    @5
    @7
    @3
    @6
    wceq
    @4
    @6
    cdm
    #
    wceq
    @26
    @5
    wi
    #
    @6
    @2
    cG
    fdm
    @3
    @6
    dmeq
    @28
    @27
    @4
    @26
    @27
    @4
    wceq
    @5
    @26
    @27
    @2
    @4
    @26
    @2
    c0
    wne
    @27
    @2
    wceq
    @2
    c0
    df-ne
    @2
    @2
    dmxp
    sylbir
    eqeq1d
    biimpcd
    eqcoms
    3syl
    com12
    pm2.61i
    pm4.71ri
    exbii
    syl6bb
    @0
    @3
    cvv
    wcel
    @4
    cvv
    wcel
    @9
    @11
    wb
    cG
    cA
    dmexg
    @3
    cvv
    dmexg
    @7
    @11
    vt
    @4
    cvv
    @5
    @7
    @4
    @4
    cxp
    #
    @4
    cG
    wf
    #
    @11
    @6
    @29
    wceq
    #
    @5
    @7
    @30
    wb
    @5
    @31
    @2
    @4
    @2
    @4
    xpeq12
    anidms
    @6
    @2
    @29
    @4
    cG
    feq23
    mpancom
    @29
    @4
    @10
    cX
    cG
    @4
    cX
    @4
    cX
    cX
    @4
    ismgmOLD.1
    eqcomi
    #
    @32
    xpeq12i
    @32
    feq23i
    syl6bb
    ceqsexgv
    3syl
    bitrd
end
