include "cc0.mm"
include "c1.mm"
include "cicc.mm"
include "co.mm"
include "cv.mm"
include "cmin.mm"
include "cfv.mm"
include "cmpt.mm"
include "cpco.mm"
include "csn.mm"
include "cxp.mm"
include "cphtpc.mm"
include "wbr.mm"
include "csconn.mm"
include "wcel.mm"
include "cii.mm"
include "ccn.mm"
include "wceq.mm"
include "w3a.mm"
include "eqid.mm"
include "pcorevcl.mm"
include "syl.mm"
include "simp1d.mm"
include "simp2d.mm"
include "eqtr4d.mm"
include "pcocn.mm"
include "pco0.mm"
include "pco1.mm"
include "simp3d.mm"
include "sconnpht.mm"
include "syl3anc.mm"
include "sneqd.mm"
include "xpeq2d.mm"
include "breqtrd.mm"
include "pcophtb.mm"
include "mpbid.mm"

theorem sconnpht2
  let wph: wff ph
  let cF: class F
  let cG: class G
  let cJ: class J
  let vx: setvar x
  assume sconnpht2.1: |- ( ph -> J e. SConn )
  assume sconnpht2.2: |- ( ph -> F e. ( II Cn J ) )
  assume sconnpht2.3: |- ( ph -> G e. ( II Cn J ) )
  assume sconnpht2.4: |- ( ph -> ( F ` 0 ) = ( G ` 0 ) )
  assume sconnpht2.5: |- ( ph -> ( F ` 1 ) = ( G ` 1 ) )


  assert |- ( ph -> F ( ~=ph ` J ) G )

  proof
    wph
    cF
    vx
    cc0
    c1
    cicc
    co
    #
    c1
    vx
    cv
    cmin
    co
    cG
    cfv
    cmpt
    #
    cJ
    cpco
    cfv
    co
    #
    @0
    cc0
    cF
    cfv
    #
    csn
    #
    cxp
    #
    cJ
    cphtpc
    cfv
    #
    wbr
    cF
    cG
    @6
    wbr
    wph
    @2
    @0
    cc0
    @2
    cfv
    #
    csn
    #
    cxp
    #
    @5
    @6
    wph
    cJ
    csconn
    wcel
    @2
    cii
    cJ
    ccn
    co
    #
    wcel
    @7
    c1
    @2
    cfv
    #
    wceq
    @2
    @9
    @6
    wbr
    sconnpht2.1
    wph
    cF
    @1
    cJ
    sconnpht2.2
    wph
    @1
    @10
    wcel
    #
    cc0
    @1
    cfv
    #
    c1
    cG
    cfv
    #
    wceq
    #
    c1
    @1
    cfv
    #
    cc0
    cG
    cfv
    #
    wceq
    #
    wph
    cG
    @10
    wcel
    @12
    @15
    @18
    w3a
    sconnpht2.3
    vx
    cG
    @1
    cJ
    @1
    eqid
    #
    pcorevcl
    syl
    #
    simp1d
    #
    wph
    c1
    cF
    cfv
    @14
    @13
    sconnpht2.5
    wph
    @12
    @15
    @18
    @20
    simp2d
    eqtr4d
    pcocn
    wph
    @7
    @3
    @11
    wph
    cF
    @1
    cJ
    sconnpht2.2
    @21
    pco0
    #
    wph
    @11
    @16
    @3
    wph
    cF
    @1
    cJ
    sconnpht2.2
    @21
    pco1
    wph
    @3
    @17
    @16
    sconnpht2.4
    wph
    @12
    @15
    @18
    @20
    simp3d
    eqtr4d
    eqtr4d
    eqtr4d
    @2
    cJ
    sconnpht
    syl3anc
    wph
    @8
    @4
    @0
    wph
    @7
    @3
    @22
    sneqd
    xpeq2d
    breqtrd
    wph
    vx
    @5
    cF
    cG
    @1
    cJ
    @19
    @5
    eqid
    sconnpht2.2
    sconnpht2.3
    sconnpht2.4
    sconnpht2.5
    pcophtb
    mpbid
end
