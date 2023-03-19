include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cn.mm"
include "wcel.mm"
include "cvv.mm"
include "cv.mm"
include "cmpt.mm"
include "crdg.mm"
include "com.mm"
include "cres.mm"
include "crn.mm"
include "cfv.mm"
include "wceq.mm"
include "wrex.mm"
include "wfn.mm"
include "wb.mm"
include "frfnom.mm"
include "fvelrnb.mm"
include "ax-mp.mm"
include "csuc.mm"
include "ovex.mm"
include "eqid.mm"
include "oveq1.mm"
include "frsucmpt2.mm"
include "mpan2.mm"
include "peano2.mm"
include "fnfvelrn.mm"
include "sylancr.mm"
include "cima.mm"
include "df-nn.mm"
include "df-ima.mm"
include "eqtri.mm"
include "syl6eleqr.mm"
include "eqeltrrd.mm"
include "eleq1d.mm"
include "syl5ibcom.mm"
include "rexlimiv.mm"
include "sylbi.mm"
include "eleq2s.mm"

theorem peano2nn
  let cA: class A
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( A e. NN -> ( A + 1 ) e. NN )

  proof
    cA
    c1
    caddc
    co
    #
    cn
    wcel
    #
    cA
    vx
    cvv
    vx
    cv
    #
    c1
    caddc
    co
    #
    cmpt
    #
    c1
    crdg
    #
    com
    cres
    #
    crn
    #
    cn
    cA
    @7
    wcel
    #
    vy
    cv
    #
    @6
    cfv
    #
    cA
    wceq
    #
    vy
    com
    wrex
    #
    @1
    @6
    com
    wfn
    #
    @8
    @12
    wb
    c1
    @4
    frfnom
    #
    vy
    com
    cA
    @6
    fvelrnb
    ax-mp
    @11
    @1
    vy
    com
    @9
    com
    wcel
    #
    @10
    c1
    caddc
    co
    #
    cn
    wcel
    @11
    @1
    @15
    @9
    csuc
    #
    @6
    cfv
    #
    @16
    cn
    @15
    @16
    cvv
    wcel
    @18
    @16
    wceq
    @10
    c1
    caddc
    ovex
    vx
    vz
    c1
    @9
    @3
    @16
    vz
    cv
    #
    c1
    caddc
    co
    @6
    cvv
    @6
    eqid
    @19
    @2
    c1
    caddc
    oveq1
    @19
    @10
    c1
    caddc
    oveq1
    frsucmpt2
    mpan2
    @15
    @18
    @7
    cn
    @15
    @13
    @17
    com
    wcel
    @18
    @7
    wcel
    @14
    @9
    peano2
    com
    @17
    @6
    fnfvelrn
    sylancr
    cn
    @5
    com
    cima
    @7
    vx
    df-nn
    @5
    com
    df-ima
    eqtri
    #
    syl6eleqr
    eqeltrrd
    @11
    @16
    @0
    cn
    @10
    cA
    c1
    caddc
    oveq1
    eleq1d
    syl5ibcom
    rexlimiv
    sylbi
    @20
    eleq2s
end
