include "cmbf.mm"
include "wcel.mm"
include "cre.mm"
include "ccom.mm"
include "ccnv.mm"
include "cr.mm"
include "cima.mm"
include "cdm.mm"
include "cvol.mm"
include "wf.mm"
include "wceq.mm"
include "cc.mm"
include "ref.mm"
include "mbff.mm"
include "fco.mm"
include "sylancr.mm"
include "fimacnv.mm"
include "syl.mm"
include "cioo.mm"
include "crn.mm"
include "cv.mm"
include "wral.mm"
include "cmnf.mm"
include "cpnf.mm"
include "co.mm"
include "ioomax.mm"
include "cxr.mm"
include "cxp.mm"
include "wfn.mm"
include "cpw.mm"
include "ioof.mm"
include "ffn.mm"
include "ax-mp.mm"
include "mnfxr.mm"
include "pnfxr.mm"
include "fnovrn.mm"
include "mp3an.mm"
include "eqeltrri.mm"
include "cim.mm"
include "wa.mm"
include "cpm.mm"
include "ismbf1.mm"
include "simprbi.mm"
include "simpl.mm"
include "ralimi.mm"
include "imaeq2.mm"
include "eleq1d.mm"
include "rspcv.mm"
include "mpsyl.mm"
include "eqeltrrd.mm"

theorem mbfdm
  let cF: class F
  let vf: setvar f
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( F e. MblFn -> dom F e. dom vol )

  proof
    cF
    cmbf
    wcel
    #
    cre
    cF
    ccom
    #
    ccnv
    #
    cr
    cima
    #
    cF
    cdm
    #
    cvol
    cdm
    #
    @0
    @4
    cr
    @1
    wf
    #
    @3
    @4
    wceq
    @0
    cc
    cr
    cre
    wf
    @4
    cc
    cF
    wf
    @6
    ref
    cF
    mbff
    @4
    cc
    cr
    cre
    cF
    fco
    sylancr
    @4
    cr
    @1
    fimacnv
    syl
    cr
    cioo
    crn
    #
    wcel
    @0
    @2
    vx
    cv
    #
    cima
    #
    @5
    wcel
    #
    vx
    @7
    wral
    #
    @3
    @5
    wcel
    #
    cmnf
    cpnf
    cioo
    co
    #
    cr
    @7
    ioomax
    cioo
    cxr
    cxr
    cxp
    #
    wfn
    #
    cmnf
    cxr
    wcel
    cpnf
    cxr
    wcel
    @13
    @7
    wcel
    @14
    cr
    cpw
    #
    cioo
    wf
    @15
    ioof
    @14
    @16
    cioo
    ffn
    ax-mp
    mnfxr
    pnfxr
    cxr
    cxr
    cmnf
    cpnf
    cioo
    fnovrn
    mp3an
    eqeltrri
    @0
    @10
    cim
    cF
    ccom
    ccnv
    @8
    cima
    @5
    wcel
    #
    wa
    #
    vx
    @7
    wral
    #
    @11
    @0
    cF
    cc
    cr
    cpm
    co
    wcel
    @19
    vx
    cF
    ismbf1
    simprbi
    @18
    @10
    vx
    @7
    @10
    @17
    simpl
    ralimi
    syl
    @10
    @12
    vx
    cr
    @7
    @8
    cr
    wceq
    @9
    @3
    @5
    @8
    cr
    @2
    imaeq2
    eleq1d
    rspcv
    mpsyl
    eqeltrrd
end
