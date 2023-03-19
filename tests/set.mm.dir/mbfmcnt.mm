include "wcel.mm"
include "cpw.mm"
include "cbrsiga.mm"
include "cmbfm.mm"
include "co.mm"
include "cuni.mm"
include "cmap.mm"
include "cr.mm"
include "cv.mm"
include "ccnv.mm"
include "cima.mm"
include "wral.mm"
include "wa.mm"
include "csiga.mm"
include "cfv.mm"
include "crn.mm"
include "pwsiga.mm"
include "elrnsiga.mm"
include "syl.mm"
include "brsigarn.mm"
include "mp1i.mm"
include "ismbfm.mm"
include "wfn.mm"
include "wf.mm"
include "cvv.mm"
include "wb.mm"
include "unibrsiga.mm"
include "reex.mm"
include "eqeltri.mm"
include "unipw.mm"
include "elex.mm"
include "syl5eqel.mm"
include "elmapg.mm"
include "sylancr.mm"
include "feq2i.mm"
include "syl6bb.mm"
include "ffn.mm"
include "syl6bi.mm"
include "wss.mm"
include "elpreima.mm"
include "simpl.mm"
include "ssrdv.mm"
include "vex.mm"
include "cnvex.mm"
include "imaexg.mm"
include "ax-mp.mm"
include "elpw.mm"
include "sylibr.mm"
include "ralrimivw.mm"
include "syl6.mm"
include "pm4.71d.mm"
include "bitr4d.mm"
include "eqrdv.mm"
include "oveq12i.mm"
include "syl6eq.mm"

theorem mbfmcnt
  let cO: class O
  let cV: class V
  let vf: setvar f
  let vx: setvar x
  let vy: setvar y


  assert |- ( O e. V -> ( ~P O MblFnM BrSiga ) = ( RR ^m O ) )

  proof
    cO
    cV
    wcel
    #
    cO
    cpw
    #
    cbrsiga
    cmbfm
    co
    #
    cbrsiga
    cuni
    #
    @1
    cuni
    #
    cmap
    co
    #
    cr
    cO
    cmap
    co
    @0
    vf
    @2
    @5
    @0
    vf
    cv
    #
    @2
    wcel
    @6
    @5
    wcel
    #
    @6
    ccnv
    #
    vx
    cv
    #
    cima
    #
    @1
    wcel
    #
    vx
    cbrsiga
    wral
    #
    wa
    @7
    @0
    vx
    @1
    cbrsiga
    @6
    @0
    @1
    cO
    csiga
    cfv
    wcel
    @1
    csiga
    crn
    cuni
    #
    wcel
    cO
    cV
    pwsiga
    @1
    cO
    elrnsiga
    syl
    cbrsiga
    cr
    csiga
    cfv
    wcel
    cbrsiga
    @13
    wcel
    @0
    brsigarn
    cbrsiga
    cr
    elrnsiga
    mp1i
    ismbfm
    @0
    @7
    @12
    @0
    @7
    @6
    cO
    wfn
    #
    @12
    @0
    @7
    cO
    @3
    @6
    wf
    #
    @14
    @0
    @7
    @4
    @3
    @6
    wf
    #
    @15
    @0
    @3
    cvv
    wcel
    @4
    cvv
    wcel
    @7
    @16
    wb
    @3
    cr
    cvv
    unibrsiga
    reex
    eqeltri
    @0
    @4
    cO
    cvv
    cO
    unipw
    #
    cO
    cV
    elex
    syl5eqel
    @3
    @4
    @6
    cvv
    cvv
    elmapg
    sylancr
    @4
    cO
    @3
    @6
    @17
    feq2i
    syl6bb
    cO
    @3
    @6
    ffn
    syl6bi
    @14
    @11
    vx
    cbrsiga
    @14
    @10
    cO
    wss
    @11
    @14
    vy
    @10
    cO
    @14
    vy
    cv
    #
    @10
    wcel
    @18
    cO
    wcel
    #
    @18
    @6
    cfv
    @9
    wcel
    #
    wa
    @19
    cO
    @18
    @9
    @6
    elpreima
    @19
    @20
    simpl
    syl6bi
    ssrdv
    @10
    cO
    @8
    cvv
    wcel
    @10
    cvv
    wcel
    @6
    vf
    vex
    cnvex
    @8
    @9
    cvv
    imaexg
    ax-mp
    elpw
    sylibr
    ralrimivw
    syl6
    pm4.71d
    bitr4d
    eqrdv
    @3
    cr
    @4
    cO
    cmap
    unibrsiga
    @17
    oveq12i
    syl6eq
end
