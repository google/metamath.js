include "cr.mm"
include "cres.mm"
include "cv.mm"
include "cpnf.mm"
include "cico.mm"
include "co.mm"
include "cima.mm"
include "cxr.mm"
include "cin.mm"
include "clt.mm"
include "csup.mm"
include "cmpt.mm"
include "crn.mm"
include "cinf.mm"
include "clsp.mm"
include "cfv.mm"
include "wceq.mm"
include "wcel.mm"
include "wss.mm"
include "id.mm"
include "pnfxr.mm"
include "a1i.mm"
include "icossre.mm"
include "syl2anc.mm"
include "resima2.mm"
include "syl.mm"
include "ineq1d.mm"
include "supeq1d.mm"
include "mpteq2ia.mm"
include "rneqd.mm"
include "infeq1d.mm"
include "cvv.mm"
include "resexd.mm"
include "eqid.mm"
include "limsupval.mm"
include "3eqtr4d.mm"

theorem limsupresre
  let wph: wff ph
  let cF: class F
  let cV: class V
  let vk: setvar k
  assume limsupresre.1: |- ( ph -> F e. V )


  assert |- ( ph -> ( limsup ` ( F |` RR ) ) = ( limsup ` F ) )

  proof
    wph
    vk
    cr
    cF
    cr
    cres
    #
    vk
    cv
    #
    cpnf
    cico
    co
    #
    cima
    #
    cxr
    cin
    #
    cxr
    clt
    csup
    #
    cmpt
    #
    crn
    #
    cxr
    clt
    cinf
    #
    vk
    cr
    cF
    @2
    cima
    #
    cxr
    cin
    #
    cxr
    clt
    csup
    #
    cmpt
    #
    crn
    #
    cxr
    clt
    cinf
    #
    @0
    clsp
    cfv
    #
    cF
    clsp
    cfv
    #
    wph
    cxr
    @7
    @13
    clt
    wph
    @6
    @12
    @6
    @12
    wceq
    wph
    vk
    cr
    @5
    @11
    @1
    cr
    wcel
    #
    cxr
    @4
    @10
    clt
    @17
    @3
    @9
    cxr
    @17
    @2
    cr
    wss
    #
    @3
    @9
    wceq
    @17
    @17
    cpnf
    cxr
    wcel
    #
    @18
    @17
    id
    @19
    @17
    pnfxr
    a1i
    @1
    cpnf
    icossre
    syl2anc
    cF
    @2
    cr
    resima2
    syl
    ineq1d
    supeq1d
    mpteq2ia
    a1i
    rneqd
    infeq1d
    wph
    @0
    cvv
    wcel
    @15
    @8
    wceq
    wph
    cF
    cr
    cV
    limsupresre.1
    resexd
    vk
    @0
    @6
    cvv
    @6
    eqid
    limsupval
    syl
    wph
    cF
    cV
    wcel
    @16
    @14
    wceq
    limsupresre.1
    vk
    cF
    @12
    cV
    @12
    eqid
    limsupval
    syl
    3eqtr4d
end
