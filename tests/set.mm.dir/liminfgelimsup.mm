include "clsp.mm"
include "cfv.mm"
include "clsi.mm"
include "cle.mm"
include "wbr.mm"
include "wceq.mm"
include "wa.mm"
include "cxr.mm"
include "wcel.mm"
include "liminfcld.mm"
include "adantr.mm"
include "limsupcld.mm"
include "liminflelimsup.mm"
include "simpr.mm"
include "xrletrid.mm"
include "id.mm"
include "eqcomd.mm"
include "adantl.mm"
include "xreqled.mm"
include "impbida.mm"

theorem liminfgelimsup
  let wph: wff ph
  let vj: setvar j
  let vk: setvar k
  let cF: class F
  let cV: class V
  let vx: setvar x
  assume liminfgelimsup.1: |- ( ph -> F e. V )
  assume liminfgelimsup.2: |- ( ph -> A. k e. RR E. j e. ( k [,) +oo ) ( ( F " ( j [,) +oo ) ) i^i RR* ) =/= (/) )

  disjoint F j
  disjoint F k
  disjoint j k
  disjoint k x
  assert |- ( ph -> ( ( limsup ` F ) <_ ( liminf ` F ) <-> ( liminf ` F ) = ( limsup ` F ) ) )

  proof
    wph
    cF
    clsp
    cfv
    #
    cF
    clsi
    cfv
    #
    cle
    wbr
    #
    @1
    @0
    wceq
    #
    wph
    @2
    wa
    @1
    @0
    wph
    @1
    cxr
    wcel
    @2
    wph
    cF
    cV
    liminfgelimsup.1
    liminfcld
    adantr
    wph
    @0
    cxr
    wcel
    #
    @2
    wph
    cF
    cV
    liminfgelimsup.1
    limsupcld
    #
    adantr
    wph
    @1
    @0
    cle
    wbr
    @2
    wph
    vj
    vk
    cF
    cV
    liminfgelimsup.1
    liminfgelimsup.2
    liminflelimsup
    adantr
    wph
    @2
    simpr
    xrletrid
    wph
    @3
    wa
    @0
    @1
    wph
    @4
    @3
    @5
    adantr
    @3
    @0
    @1
    wceq
    wph
    @3
    @1
    @0
    @3
    id
    eqcomd
    adantl
    xreqled
    impbida
end
