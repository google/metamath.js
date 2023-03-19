include "cvol.mm"
include "cdm.mm"
include "cbrsiga.mm"
include "cmbfm.mm"
include "co.mm"
include "wcel.mm"
include "cmbf.mm"
include "ccnv.mm"
include "cv.mm"
include "cima.mm"
include "cioo.mm"
include "crn.mm"
include "wral.mm"
include "wss.mm"
include "ctg.mm"
include "cfv.mm"
include "csigagen.mm"
include "ctb.mm"
include "retopbas.mm"
include "bastg.mm"
include "ax-mp.mm"
include "ctop.mm"
include "retop.mm"
include "sssigagen.mm"
include "sstri.mm"
include "df-brsiga.mm"
include "sseqtr4i.mm"
include "cuni.mm"
include "cmap.mm"
include "wceq.mm"
include "wa.mm"
include "wb.mm"
include "eqid.mm"
include "cr.mm"
include "csiga.mm"
include "dmvlsiga.mm"
include "elrnsiga.mm"
include "mp1i.mm"
include "brsigarn.mm"
include "ismbfm.mm"
include "simprbi.mm"
include "ssralv.mm"
include "mpsyl.mm"
include "wf.mm"
include "simplbi.mm"
include "elmapi.mm"
include "unibrsiga.mm"
include "unidmvol.mm"
include "oveq12i.mm"
include "eleq2s.mm"
include "ismbf.mm"
include "3syl.mm"
include "mpbird.mm"

theorem elmbfmvol2
  let cF: class F
  let vx: setvar x


  assert |- ( F e. ( dom vol MblFnM BrSiga ) -> F e. MblFn )

  proof
    cF
    cvol
    cdm
    #
    cbrsiga
    cmbfm
    co
    wcel
    #
    cF
    cmbf
    wcel
    #
    cF
    ccnv
    vx
    cv
    cima
    @0
    wcel
    #
    vx
    cioo
    crn
    #
    wral
    #
    @4
    cbrsiga
    wss
    @1
    @3
    vx
    cbrsiga
    wral
    #
    @5
    @4
    @4
    ctg
    cfv
    #
    csigagen
    cfv
    #
    cbrsiga
    @4
    @7
    @8
    @4
    ctb
    wcel
    @4
    @7
    wss
    retopbas
    @4
    ctb
    bastg
    ax-mp
    @7
    ctop
    wcel
    @7
    @8
    wss
    retop
    @7
    ctop
    sssigagen
    ax-mp
    sstri
    df-brsiga
    sseqtr4i
    @1
    cF
    cbrsiga
    cuni
    #
    @0
    cuni
    #
    cmap
    co
    #
    wcel
    #
    @6
    cvol
    cvol
    wceq
    #
    @1
    @12
    @6
    wa
    wb
    cvol
    eqid
    @13
    vx
    @0
    cbrsiga
    cF
    @0
    cr
    csiga
    cfv
    #
    wcel
    @0
    csiga
    crn
    cuni
    #
    wcel
    @13
    dmvlsiga
    @0
    cr
    elrnsiga
    mp1i
    cbrsiga
    @14
    wcel
    cbrsiga
    @15
    wcel
    @13
    brsigarn
    cbrsiga
    cr
    elrnsiga
    mp1i
    ismbfm
    ax-mp
    #
    simprbi
    @3
    vx
    @4
    cbrsiga
    ssralv
    mpsyl
    @1
    @12
    cr
    cr
    cF
    wf
    #
    @2
    @5
    wb
    @1
    @12
    @6
    @16
    simplbi
    @17
    cF
    cr
    cr
    cmap
    co
    @11
    cF
    cr
    cr
    elmapi
    @9
    cr
    @10
    cr
    cmap
    unibrsiga
    unidmvol
    oveq12i
    eleq2s
    vx
    cr
    cF
    ismbf
    3syl
    mpbird
end
