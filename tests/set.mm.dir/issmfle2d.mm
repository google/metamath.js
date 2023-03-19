include "cv.mm"
include "cr.mm"
include "wcel.mm"
include "wa.mm"
include "ccnv.mm"
include "cmnf.mm"
include "cioc.mm"
include "co.mm"
include "cima.mm"
include "cfv.mm"
include "cle.mm"
include "wbr.mm"
include "crab.mm"
include "crest.mm"
include "wf.mm"
include "adantr.mm"
include "cxr.mm"
include "rexr.mm"
include "adantl.mm"
include "preimaiocmnf.mm"
include "eqeltrrd.mm"
include "issmfled.mm"

theorem issmfle2d
  let wph: wff ph
  let cD: class D
  let cS: class S
  let cF: class F
  let va: setvar a
  let vx: setvar x
  let vk: setvar k
  assume issmfle2d.a: |- F/ a ph
  assume issmfle2d.s: |- ( ph -> S e. SAlg )
  assume issmfle2d.d: |- ( ph -> D C_ U. S )
  assume issmfle2d.f: |- ( ph -> F : D --> RR )
  assume issmfle2d.l: |- ( ( ph /\ a e. RR ) -> ( `' F " ( -oo (,] a ) ) e. ( S |`t D ) )

  disjoint F a
  disjoint S a
  disjoint D x
  disjoint F x
  disjoint a x
  disjoint ph x
  disjoint k x
  assert |- ( ph -> F e. ( SMblFn ` S ) )

  proof
    wph
    vx
    cD
    cS
    cF
    va
    issmfle2d.a
    issmfle2d.s
    issmfle2d.d
    issmfle2d.f
    wph
    va
    cv
    #
    cr
    wcel
    #
    wa
    #
    cF
    ccnv
    cmnf
    @0
    cioc
    co
    cima
    vx
    cv
    cF
    cfv
    @0
    cle
    wbr
    vx
    cD
    crab
    cS
    cD
    crest
    co
    @2
    vx
    cD
    @0
    cF
    wph
    cD
    cr
    cF
    wf
    @1
    issmfle2d.f
    adantr
    @1
    @0
    cxr
    wcel
    wph
    @0
    rexr
    adantl
    preimaiocmnf
    issmfle2d.l
    eqeltrrd
    issmfled
end
