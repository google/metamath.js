include "cv.mm"
include "cpnf.mm"
include "cico.mm"
include "co.mm"
include "cima.mm"
include "cxr.mm"
include "cin.mm"
include "c0.mm"
include "wne.mm"
include "wrex.mm"
include "cr.mm"
include "wral.mm"
include "nfv.mm"
include "wceq.mm"
include "oveq1.mm"
include "rexeqdv.mm"
include "wb.mm"
include "imaeq2d.mm"
include "ineq1d.mm"
include "neeq1d.mm"
include "cbvrexv.mm"
include "a1i.mm"
include "bitrd.mm"
include "cbvral.mm"
include "sylib.mm"
include "liminflelimsuplem.mm"

theorem liminflelimsup
  let wph: wff ph
  let vj: setvar j
  let vk: setvar k
  let cF: class F
  let cV: class V
  let vi: setvar i
  let vl: setvar l
  let vx: setvar x
  assume liminflelimsup.1: |- ( ph -> F e. V )
  assume liminflelimsup.2: |- ( ph -> A. k e. RR E. j e. ( k [,) +oo ) ( ( F " ( j [,) +oo ) ) i^i RR* ) =/= (/) )

  disjoint F j
  disjoint F k
  disjoint j k
  disjoint F i
  disjoint F l
  disjoint i j
  disjoint i k
  disjoint i l
  disjoint j l
  disjoint k l
  disjoint l ph
  disjoint k x
  assert |- ( ph -> ( liminf ` F ) <_ ( limsup ` F ) )

  proof
    wph
    vl
    vi
    cF
    cV
    liminflelimsup.1
    wph
    cF
    vj
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
    c0
    wne
    #
    vj
    vk
    cv
    #
    cpnf
    cico
    co
    #
    wrex
    #
    vk
    cr
    wral
    cF
    vl
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
    c0
    wne
    #
    vl
    vi
    cv
    #
    cpnf
    cico
    co
    #
    wrex
    #
    vi
    cr
    wral
    liminflelimsup.2
    @7
    @15
    vk
    vi
    cr
    @7
    vi
    nfv
    @15
    vk
    nfv
    @5
    @13
    wceq
    #
    @7
    @4
    vj
    @14
    wrex
    #
    @15
    @16
    @4
    vj
    @6
    @14
    @5
    @13
    cpnf
    cico
    oveq1
    rexeqdv
    @17
    @15
    wb
    @16
    @4
    @12
    vj
    vl
    @14
    @0
    @8
    wceq
    #
    @3
    @11
    c0
    @18
    @2
    @10
    cxr
    @18
    @1
    @9
    cF
    @0
    @8
    cpnf
    cico
    oveq1
    imaeq2d
    ineq1d
    neeq1d
    cbvrexv
    a1i
    bitrd
    cbvral
    sylib
    liminflelimsuplem
end
