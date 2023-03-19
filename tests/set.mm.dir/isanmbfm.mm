include "cv.mm"
include "cuni.mm"
include "cmap.mm"
include "co.mm"
include "wcel.mm"
include "ccnv.mm"
include "cima.mm"
include "wral.mm"
include "wa.mm"
include "csiga.mm"
include "crn.mm"
include "wrex.mm"
include "cmbfm.mm"
include "ismbfm.mm"
include "mpbid.mm"
include "wceq.mm"
include "unieq.mm"
include "oveq2d.mm"
include "eleq2d.mm"
include "eleq2.mm"
include "ralbidv.mm"
include "anbi12d.mm"
include "oveq1d.mm"
include "raleq.mm"
include "rspc2ev.mm"
include "syl3anc.mm"
include "elunirnmbfm.mm"
include "sylibr.mm"

theorem isanmbfm
  let wph: wff ph
  let cS: class S
  let cT: class T
  let cF: class F
  let vs: setvar s
  let vt: setvar t
  let vx: setvar x
  assume mbfmf.1: |- ( ph -> S e. U. ran sigAlgebra )
  assume mbfmf.2: |- ( ph -> T e. U. ran sigAlgebra )
  assume mbfmf.3: |- ( ph -> F e. ( S MblFnM T ) )


  assert |- ( ph -> F e. U. ran MblFnM )

  proof
    wph
    cF
    vt
    cv
    #
    cuni
    #
    vs
    cv
    #
    cuni
    #
    cmap
    co
    #
    wcel
    #
    cF
    ccnv
    vx
    cv
    cima
    #
    @2
    wcel
    #
    vx
    @0
    wral
    #
    wa
    #
    vt
    csiga
    crn
    cuni
    #
    wrex
    vs
    @10
    wrex
    #
    cF
    cmbfm
    crn
    cuni
    wcel
    wph
    cS
    @10
    wcel
    cT
    @10
    wcel
    cF
    cT
    cuni
    #
    cS
    cuni
    #
    cmap
    co
    #
    wcel
    #
    @6
    cS
    wcel
    #
    vx
    cT
    wral
    #
    wa
    #
    @11
    mbfmf.1
    mbfmf.2
    wph
    cF
    cS
    cT
    cmbfm
    co
    wcel
    @18
    mbfmf.3
    wph
    vx
    cS
    cT
    cF
    mbfmf.1
    mbfmf.2
    ismbfm
    mpbid
    @9
    @18
    cF
    @1
    @13
    cmap
    co
    #
    wcel
    #
    @16
    vx
    @0
    wral
    #
    wa
    vs
    vt
    cS
    cT
    @10
    @10
    @2
    cS
    wceq
    #
    @5
    @20
    @8
    @21
    @22
    @4
    @19
    cF
    @22
    @3
    @13
    @1
    cmap
    @2
    cS
    unieq
    oveq2d
    eleq2d
    @22
    @7
    @16
    vx
    @0
    @2
    cS
    @6
    eleq2
    ralbidv
    anbi12d
    @0
    cT
    wceq
    #
    @20
    @15
    @21
    @17
    @23
    @19
    @14
    cF
    @23
    @1
    @12
    @13
    cmap
    @0
    cT
    unieq
    oveq1d
    eleq2d
    @16
    vx
    @0
    cT
    raleq
    anbi12d
    rspc2ev
    syl3anc
    vx
    vt
    cF
    vs
    elunirnmbfm
    sylibr
end
