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
include "cvv.mm"
include "wcel.mm"
include "wceq.mm"
include "fexd.mm"
include "eqid.mm"
include "limsupval.mm"
include "syl.mm"
include "a1i.mm"
include "wss.mm"
include "fimassd.mm"
include "df-ss.mm"
include "sylib.mm"
include "eqcomd.mm"
include "supeq1d.mm"
include "adantr.mm"
include "mpteq2da.mm"
include "eqtr2d.mm"
include "rneqd.mm"
include "infeq1d.mm"
include "eqtrd.mm"

theorem limsupval3
  let wph: wff ph
  let cA: class A
  let vk: setvar k
  let cF: class F
  let cG: class G
  let cV: class V
  assume limsupval3.1: |- F/ k ph
  assume limsupval3.2: |- ( ph -> A e. V )
  assume limsupval3.3: |- ( ph -> F : A --> RR* )
  assume limsupval3.4: |- G = ( k e. RR |-> sup ( ( F " ( k [,) +oo ) ) , RR* , < ) )

  disjoint F k
  assert |- ( ph -> ( limsup ` F ) = inf ( ran G , RR* , < ) )

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
    #
    cxr
    clt
    cinf
    #
    cG
    crn
    #
    cxr
    clt
    cinf
    wph
    cF
    cvv
    wcel
    @0
    @8
    wceq
    wph
    cA
    cxr
    cV
    cF
    limsupval3.3
    limsupval3.2
    fexd
    vk
    cF
    @6
    cvv
    @6
    eqid
    limsupval
    syl
    wph
    cxr
    @7
    @9
    clt
    wph
    @6
    cG
    wph
    cG
    vk
    cr
    @3
    cxr
    clt
    csup
    #
    cmpt
    #
    @6
    cG
    @11
    wceq
    wph
    limsupval3.4
    a1i
    wph
    vk
    cr
    @10
    @5
    limsupval3.1
    wph
    @10
    @5
    wceq
    @1
    cr
    wcel
    wph
    cxr
    @3
    @4
    clt
    wph
    @4
    @3
    wph
    @3
    cxr
    wss
    @4
    @3
    wceq
    wph
    cA
    cxr
    cF
    @2
    limsupval3.3
    fimassd
    @3
    cxr
    df-ss
    sylib
    eqcomd
    supeq1d
    adantr
    mpteq2da
    eqtr2d
    rneqd
    infeq1d
    eqtrd
end
