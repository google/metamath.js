include "crn.mm"
include "cuni.mm"
include "cxp.mm"
include "cdom.mm"
include "wbr.mm"
include "cen.mm"
include "com.mm"
include "cvv.mm"
include "wcel.mm"
include "cv.mm"
include "wral.mm"
include "wfn.mm"
include "cfn.mm"
include "wf.mm"
include "ffn.mm"
include "syl.mm"
include "fnex.mm"
include "syl2anc.mm"
include "rnexg.mm"
include "wss.mm"
include "frn.mm"
include "dfss3.mm"
include "sylib.mm"
include "csdm.mm"
include "isfinite.mm"
include "sdomdom.mm"
include "sylbi.mm"
include "ralimi.mm"
include "3syl.mm"
include "unidom.mm"
include "fnrndomg.mm"
include "sylc.mm"
include "omex.mm"
include "xpdom1.mm"
include "domtr.mm"
include "wn.mm"
include "wb.mm"
include "infinf.mm"
include "mpbid.mm"
include "xpdom2g.mm"
include "infxpidm.mm"
include "domentr.mm"

theorem unirnfdomd
  let wph: wff ph
  let cT: class T
  let cF: class F
  let cV: class V
  let vx: setvar x
  assume unirnfdomd.1: |- ( ph -> F : T --> Fin )
  assume unirnfdomd.2: |- ( ph -> -. T e. Fin )
  assume unirnfdomd.3: |- ( ph -> T e. V )


  assert |- ( ph -> U. ran F ~<_ T )

  proof
    wph
    cF
    crn
    #
    cuni
    #
    cT
    cT
    cxp
    #
    cdom
    wbr
    #
    @2
    cT
    cen
    wbr
    #
    @1
    cT
    cdom
    wbr
    wph
    @1
    cT
    com
    cxp
    #
    cdom
    wbr
    #
    @5
    @2
    cdom
    wbr
    #
    @3
    wph
    @1
    @0
    com
    cxp
    #
    cdom
    wbr
    #
    @8
    @5
    cdom
    wbr
    #
    @6
    wph
    @0
    cvv
    wcel
    #
    vx
    cv
    #
    com
    cdom
    wbr
    #
    vx
    @0
    wral
    #
    @9
    wph
    cF
    cvv
    wcel
    #
    @11
    wph
    cF
    cT
    wfn
    #
    cT
    cV
    wcel
    #
    @15
    wph
    cT
    cfn
    cF
    wf
    #
    @16
    unirnfdomd.1
    cT
    cfn
    cF
    ffn
    syl
    #
    unirnfdomd.3
    cT
    cV
    cF
    fnex
    syl2anc
    cF
    cvv
    rnexg
    syl
    wph
    @18
    @12
    cfn
    wcel
    #
    vx
    @0
    wral
    #
    @14
    unirnfdomd.1
    @18
    @0
    cfn
    wss
    @21
    cT
    cfn
    cF
    frn
    vx
    @0
    cfn
    dfss3
    sylib
    @20
    @13
    vx
    @0
    @20
    @12
    com
    csdm
    wbr
    @13
    @12
    isfinite
    @12
    com
    sdomdom
    sylbi
    ralimi
    3syl
    vx
    @0
    com
    cvv
    unidom
    syl2anc
    wph
    @0
    cT
    cdom
    wbr
    #
    @10
    wph
    @17
    @16
    @22
    unirnfdomd.3
    @19
    cT
    cV
    cF
    fnrndomg
    sylc
    @0
    cT
    com
    omex
    xpdom1
    syl
    @1
    @8
    @5
    domtr
    syl2anc
    wph
    @17
    com
    cT
    cdom
    wbr
    #
    @7
    unirnfdomd.3
    wph
    cT
    cfn
    wcel
    wn
    #
    @23
    unirnfdomd.2
    wph
    @17
    @24
    @23
    wb
    unirnfdomd.3
    cT
    cV
    infinf
    syl
    mpbid
    #
    com
    cT
    cT
    cV
    xpdom2g
    syl2anc
    @1
    @5
    @2
    domtr
    syl2anc
    wph
    @23
    @4
    @25
    cT
    infxpidm
    syl
    @1
    @2
    cT
    domentr
    syl2anc
end
