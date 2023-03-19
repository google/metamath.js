include "ccnv.mm"
include "cdm.mm"
include "cima.mm"
include "ccom.mm"
include "crn.mm"
include "wf.mm"
include "wfun.mm"
include "funco.mm"
include "syl2anc.mm"
include "fdmrn.mm"
include "sylib.mm"
include "wb.mm"
include "dmco.mm"
include "feq2i.mm"
include "a1i.mm"
include "mpbid.mm"
include "wss.mm"
include "rncoss.mm"
include "fssd.mm"

theorem fco3
  let wph: wff ph
  let cF: class F
  let cG: class G
  assume fco3.1: |- ( ph -> Fun F )
  assume fco3.2: |- ( ph -> Fun G )


  assert |- ( ph -> ( F o. G ) : ( `' G " dom F ) --> ran F )

  proof
    wph
    cG
    ccnv
    cF
    cdm
    cima
    #
    cF
    cG
    ccom
    #
    crn
    #
    cF
    crn
    #
    @1
    wph
    @1
    cdm
    #
    @2
    @1
    wf
    #
    @0
    @2
    @1
    wf
    #
    wph
    @1
    wfun
    #
    @5
    wph
    cF
    wfun
    cG
    wfun
    @7
    fco3.1
    fco3.2
    cF
    cG
    funco
    syl2anc
    @1
    fdmrn
    sylib
    @5
    @6
    wb
    wph
    @4
    @0
    @2
    @1
    cF
    cG
    dmco
    feq2i
    a1i
    mpbid
    @2
    @3
    wss
    wph
    cF
    cG
    rncoss
    a1i
    fssd
end
