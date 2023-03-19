include "clsp.mm"
include "cfv.mm"
include "clsi.mm"
include "cle.mm"
include "wbr.mm"
include "wceq.mm"
include "wa.mm"
include "cxr.mm"
include "wcel.mm"
include "cvv.mm"
include "cr.mm"
include "cuz.mm"
include "fvexi.mm"
include "a1i.mm"
include "fexd.mm"
include "liminfcld.mm"
include "adantr.mm"
include "limsupcld.mm"
include "frexr.mm"
include "liminflelimsupuz.mm"
include "simpr.mm"
include "xrletrid.mm"
include "id.mm"
include "eqcomd.mm"
include "adantl.mm"
include "xreqled.mm"
include "impbida.mm"

theorem liminfgelimsupuz
  let wph: wff ph
  let cF: class F
  let cM: class M
  let cZ: class Z
  let vk: setvar k
  let vx: setvar x
  assume liminfgelimsupuz.1: |- ( ph -> M e. ZZ )
  assume liminfgelimsupuz.2: |- Z = ( ZZ>= ` M )
  assume liminfgelimsupuz.3: |- ( ph -> F : Z --> RR )


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
    cvv
    wph
    cZ
    cr
    cvv
    cF
    liminfgelimsupuz.3
    cZ
    cvv
    wcel
    wph
    cZ
    cM
    cuz
    liminfgelimsupuz.2
    fvexi
    a1i
    fexd
    #
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
    cvv
    @4
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
    cF
    cM
    cZ
    liminfgelimsupuz.1
    liminfgelimsupuz.2
    wph
    cZ
    cF
    liminfgelimsupuz.3
    frexr
    liminflelimsupuz
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
    @5
    @3
    @6
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
