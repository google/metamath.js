include "clsp.mm"
include "cfv.mm"
include "cr.mm"
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
include "cle.mm"
include "wcel.mm"
include "wceq.mm"
include "eqid.mm"
include "limsupval.mm"
include "syl.mm"
include "nfv.mm"
include "wa.mm"
include "wss.mm"
include "inss2.mm"
include "a1i.mm"
include "supxrcld.mm"
include "oveq1.mm"
include "imaeq2d.mm"
include "ineq1d.mm"
include "supeq1d.mm"
include "infxrlbrnmpt2.mm"
include "eqbrtrd.mm"

theorem limsuplesup
  let wph: wff ph
  let cF: class F
  let cK: class K
  let cV: class V
  let vk: setvar k
  assume limsuplesup.1: |- ( ph -> F e. V )
  assume limsuplesup.2: |- ( ph -> K e. RR )


  assert |- ( ph -> ( limsup ` F ) <_ sup ( ( ( F " ( K [,) +oo ) ) i^i RR* ) , RR* , < ) )

  proof
    wph
    cF
    clsp
    cfv
    #
    vk
    cr
    cF
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
    cxr
    clt
    cinf
    #
    cF
    cK
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
    cle
    wph
    cF
    cV
    wcel
    @0
    @7
    wceq
    limsuplesup.1
    vk
    cF
    @6
    cV
    @6
    eqid
    limsupval
    syl
    wph
    vk
    cr
    @5
    cK
    @11
    wph
    vk
    nfv
    wph
    @1
    cr
    wcel
    wa
    #
    @4
    @4
    cxr
    wss
    @12
    @3
    cxr
    inss2
    a1i
    supxrcld
    limsuplesup.2
    wph
    @10
    @10
    cxr
    wss
    wph
    @9
    cxr
    inss2
    a1i
    supxrcld
    @1
    cK
    wceq
    #
    cxr
    @4
    @10
    clt
    @13
    @3
    @9
    cxr
    @13
    @2
    @8
    cF
    @1
    cK
    cpnf
    cico
    oveq1
    imaeq2d
    ineq1d
    supeq1d
    infxrlbrnmpt2
    eqbrtrd
end
