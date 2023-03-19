include "clsi.mm"
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
include "cinf.mm"
include "cmpt.mm"
include "crn.mm"
include "csup.mm"
include "cvv.mm"
include "wcel.mm"
include "wceq.mm"
include "fexd.mm"
include "eqid.mm"
include "liminfval.mm"
include "syl.mm"
include "a1i.mm"
include "wa.mm"
include "wss.mm"
include "fimassd.mm"
include "df-ss.mm"
include "sylib.mm"
include "eqcomd.mm"
include "adantr.mm"
include "infeq1d.mm"
include "mpteq2da.mm"
include "eqtr2d.mm"
include "rneqd.mm"
include "supeq1d.mm"
include "eqtrd.mm"

theorem liminfval5
  let wph: wff ph
  let cA: class A
  let vk: setvar k
  let cF: class F
  let cG: class G
  let cV: class V
  let vx: setvar x
  assume limsupval5.1: |- F/ k ph
  assume limsupval5.2: |- ( ph -> A e. V )
  assume limsupval5.3: |- ( ph -> F : A --> RR* )
  assume limsupval5.4: |- G = ( k e. RR |-> inf ( ( F " ( k [,) +oo ) ) , RR* , < ) )

  disjoint F k
  disjoint k x
  assert |- ( ph -> ( liminf ` F ) = sup ( ran G , RR* , < ) )

  proof
    wph
    cF
    clsi
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
    cinf
    #
    cmpt
    #
    crn
    #
    cxr
    clt
    csup
    #
    cG
    crn
    #
    cxr
    clt
    csup
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
    limsupval5.3
    limsupval5.2
    fexd
    vk
    cF
    @6
    cvv
    @6
    eqid
    liminfval
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
    cinf
    #
    cmpt
    #
    @6
    cG
    @11
    wceq
    wph
    limsupval5.4
    a1i
    wph
    vk
    cr
    @10
    @5
    limsupval5.1
    wph
    @1
    cr
    wcel
    #
    wa
    cxr
    @3
    @4
    clt
    wph
    @3
    @4
    wceq
    @12
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
    limsupval5.3
    fimassd
    @3
    cxr
    df-ss
    sylib
    eqcomd
    adantr
    infeq1d
    mpteq2da
    eqtr2d
    rneqd
    supeq1d
    eqtrd
end
