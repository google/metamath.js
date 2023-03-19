include "cc.mm"
include "cnr.mm"
include "cxp.mm"
include "df-c.mm"
include "cnp.mm"
include "cer.mm"
include "cqs.mm"
include "df-nr.mm"
include "cpw.mm"
include "cnq.mm"
include "cnpi.mm"
include "com.mm"
include "c0.mm"
include "csn.mm"
include "cdif.mm"
include "df-ni.mm"
include "wundif.mm"
include "syl5eqel.mm"
include "wunxp.mm"
include "wss.mm"
include "cv.mm"
include "elpqn.mm"
include "ssriv.mm"
include "a1i.mm"
include "wunss.mm"
include "wunpw.mm"
include "wcel.mm"
include "prpssnq.mm"
include "pssssd.mm"
include "selpw.mm"
include "sylibr.mm"
include "wer.mm"
include "enrer.mm"
include "qsss.mm"

theorem wuncn
  let wph: wff ph
  let cU: class U
  let vx: setvar x
  assume wuncn.1: |- ( ph -> U e. WUni )
  assume wuncn.2: |- ( ph -> _om e. U )


  assert |- ( ph -> CC e. U )

  proof
    wph
    cc
    cnr
    cnr
    cxp
    cU
    df-c
    wph
    cnr
    cnr
    cU
    wuncn.1
    wph
    cnr
    cnp
    cnp
    cxp
    #
    cer
    cqs
    #
    cU
    df-nr
    wph
    @0
    cpw
    @1
    cU
    wuncn.1
    wph
    @0
    cU
    wuncn.1
    wph
    cnp
    cnp
    cU
    wuncn.1
    wph
    cnq
    cpw
    #
    cnp
    cU
    wuncn.1
    wph
    cnq
    cU
    wuncn.1
    wph
    cnpi
    cnpi
    cxp
    #
    cnq
    cU
    wuncn.1
    wph
    cnpi
    cnpi
    cU
    wuncn.1
    wph
    cnpi
    com
    c0
    csn
    #
    cdif
    cU
    df-ni
    wph
    com
    @4
    cU
    wuncn.1
    wuncn.2
    wundif
    syl5eqel
    #
    @5
    wunxp
    cnq
    @3
    wss
    wph
    vx
    cnq
    @3
    vx
    cv
    #
    elpqn
    ssriv
    a1i
    wunss
    wunpw
    cnp
    @2
    wss
    wph
    vx
    cnp
    @2
    @6
    cnp
    wcel
    #
    @6
    cnq
    wss
    @6
    @2
    wcel
    @7
    @6
    cnq
    @6
    prpssnq
    pssssd
    vx
    cnq
    selpw
    sylibr
    ssriv
    a1i
    wunss
    #
    @8
    wunxp
    wunpw
    wph
    @0
    cer
    @0
    cer
    wer
    wph
    enrer
    a1i
    qsss
    wunss
    syl5eqel
    #
    @9
    wunxp
    syl5eqel
end
