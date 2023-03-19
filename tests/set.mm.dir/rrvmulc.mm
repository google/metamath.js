include "cmul.mm"
include "cofc.mm"
include "co.mm"
include "crrv.mm"
include "cfv.mm"
include "wcel.mm"
include "cdm.mm"
include "cbrsiga.mm"
include "cmbfm.mm"
include "cr.mm"
include "cv.mm"
include "cmpt.mm"
include "ccom.mm"
include "cuni.mm"
include "cvv.mm"
include "rrvvf.mm"
include "csiga.mm"
include "crn.mm"
include "cprb.mm"
include "domprobsiga.mm"
include "syl.mm"
include "uniexg.mm"
include "ofcfval4.mm"
include "brsigarn.mm"
include "elrnsiga.mm"
include "mp1i.mm"
include "rrvmbfm.mm"
include "mpbid.mm"
include "cioo.mm"
include "ctg.mm"
include "eqid.mm"
include "rmulccn.mm"
include "csigagen.mm"
include "wceq.mm"
include "df-brsiga.mm"
include "a1i.mm"
include "cnmbfm.mm"
include "mbfmco.mm"
include "eqeltrd.mm"
include "mpbird.mm"

theorem rrvmulc
  let wph: wff ph
  let cC: class C
  let cP: class P
  let cX: class X
  let vx: setvar x
  assume rrvmulc.1: |- ( ph -> P e. Prob )
  assume rrvmulc.2: |- ( ph -> X e. ( rRndVar ` P ) )
  assume rrvmulc.3: |- ( ph -> C e. RR )


  assert |- ( ph -> ( X oFC x. C ) e. ( rRndVar ` P ) )

  proof
    wph
    cX
    cC
    cmul
    cofc
    co
    #
    cP
    crrv
    cfv
    #
    wcel
    @0
    cP
    cdm
    #
    cbrsiga
    cmbfm
    co
    #
    wcel
    wph
    @0
    vx
    cr
    vx
    cv
    cC
    cmul
    co
    cmpt
    #
    cX
    ccom
    @3
    wph
    vx
    @2
    cuni
    #
    cr
    cC
    cmul
    cX
    cvv
    cr
    wph
    cP
    cX
    rrvmulc.1
    rrvmulc.2
    rrvvf
    wph
    @2
    csiga
    crn
    cuni
    #
    wcel
    #
    @5
    cvv
    wcel
    wph
    cP
    cprb
    wcel
    @7
    rrvmulc.1
    cP
    domprobsiga
    syl
    #
    @2
    @6
    uniexg
    syl
    rrvmulc.3
    ofcfval4
    wph
    @2
    cbrsiga
    cbrsiga
    cX
    @4
    @8
    cbrsiga
    cr
    csiga
    cfv
    wcel
    cbrsiga
    @6
    wcel
    wph
    brsigarn
    cbrsiga
    cr
    elrnsiga
    mp1i
    #
    @9
    wph
    cX
    @1
    wcel
    cX
    @3
    wcel
    rrvmulc.2
    wph
    cP
    cX
    rrvmulc.1
    rrvmbfm
    mpbid
    wph
    cbrsiga
    cbrsiga
    @4
    cioo
    crn
    ctg
    cfv
    #
    @10
    wph
    vx
    cC
    @10
    @10
    eqid
    rrvmulc.3
    rmulccn
    cbrsiga
    @10
    csigagen
    cfv
    wceq
    wph
    df-brsiga
    a1i
    #
    @11
    cnmbfm
    mbfmco
    eqeltrd
    wph
    cP
    @0
    rrvmulc.1
    rrvmbfm
    mpbird
end
