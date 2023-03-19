include "ccom.mm"
include "cmbfm.mm"
include "co.mm"
include "wcel.mm"
include "cuni.mm"
include "cmap.mm"
include "ccnv.mm"
include "cv.mm"
include "cima.mm"
include "wral.mm"
include "wf.mm"
include "mbfmf.mm"
include "fco.mm"
include "syl2anc.mm"
include "csiga.mm"
include "crn.mm"
include "unielsiga.mm"
include "syl.mm"
include "elmapd.mm"
include "mpbird.mm"
include "wa.mm"
include "cnvco.mm"
include "imaeq1i.mm"
include "imaco.mm"
include "eqtri.mm"
include "adantr.mm"
include "simpr.mm"
include "mbfmcnvima.mm"
include "syl5eqel.mm"
include "ralrimiva.mm"
include "ismbfm.mm"
include "mpbir2and.mm"

theorem mbfmco
  let wph: wff ph
  let cR: class R
  let cS: class S
  let cT: class T
  let cF: class F
  let cG: class G
  let va: setvar a
  assume mbfmco.1: |- ( ph -> R e. U. ran sigAlgebra )
  assume mbfmco.2: |- ( ph -> S e. U. ran sigAlgebra )
  assume mbfmco.3: |- ( ph -> T e. U. ran sigAlgebra )
  assume mbfmco.4: |- ( ph -> F e. ( R MblFnM S ) )
  assume mbfmco.5: |- ( ph -> G e. ( S MblFnM T ) )


  assert |- ( ph -> ( G o. F ) e. ( R MblFnM T ) )

  proof
    wph
    cG
    cF
    ccom
    #
    cR
    cT
    cmbfm
    co
    wcel
    @0
    cT
    cuni
    #
    cR
    cuni
    #
    cmap
    co
    wcel
    #
    @0
    ccnv
    #
    va
    cv
    #
    cima
    #
    cR
    wcel
    #
    va
    cT
    wral
    wph
    @3
    @2
    @1
    @0
    wf
    #
    wph
    cS
    cuni
    #
    @1
    cG
    wf
    @2
    @9
    cF
    wf
    @8
    wph
    cS
    cT
    cG
    mbfmco.2
    mbfmco.3
    mbfmco.5
    mbfmf
    wph
    cR
    cS
    cF
    mbfmco.1
    mbfmco.2
    mbfmco.4
    mbfmf
    @2
    @9
    @1
    cG
    cF
    fco
    syl2anc
    wph
    @1
    @2
    @0
    cT
    cR
    wph
    cT
    csiga
    crn
    cuni
    #
    wcel
    #
    @1
    cT
    wcel
    mbfmco.3
    cT
    unielsiga
    syl
    wph
    cR
    @10
    wcel
    #
    @2
    cR
    wcel
    mbfmco.1
    cR
    unielsiga
    syl
    elmapd
    mpbird
    wph
    @7
    va
    cT
    wph
    @5
    cT
    wcel
    #
    wa
    #
    @6
    cF
    ccnv
    #
    cG
    ccnv
    #
    @5
    cima
    #
    cima
    #
    cR
    @6
    @15
    @16
    ccom
    #
    @5
    cima
    @18
    @4
    @19
    @5
    cG
    cF
    cnvco
    imaeq1i
    @15
    @16
    @5
    imaco
    eqtri
    @14
    @17
    cR
    cS
    cF
    wph
    @12
    @13
    mbfmco.1
    adantr
    wph
    cS
    @10
    wcel
    @13
    mbfmco.2
    adantr
    #
    wph
    cF
    cR
    cS
    cmbfm
    co
    wcel
    @13
    mbfmco.4
    adantr
    @14
    @5
    cS
    cT
    cG
    @20
    wph
    @11
    @13
    mbfmco.3
    adantr
    wph
    cG
    cS
    cT
    cmbfm
    co
    wcel
    @13
    mbfmco.5
    adantr
    wph
    @13
    simpr
    mbfmcnvima
    mbfmcnvima
    syl5eqel
    ralrimiva
    wph
    va
    cR
    cT
    @0
    mbfmco.1
    mbfmco.3
    ismbfm
    mpbir2and
end
