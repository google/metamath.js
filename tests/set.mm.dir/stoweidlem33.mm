include "cv.mm"
include "cfv.mm"
include "cmin.mm"
include "co.mm"
include "cmpt.mm"
include "c1.mm"
include "cneg.mm"
include "cmul.mm"
include "eqid.mm"
include "stoweidlem22.mm"

theorem stoweidlem33
  let wph: wff ph
  let vx: setvar x
  let vt: setvar t
  let cA: class A
  let cT: class T
  let vf: setvar f
  let vg: setvar g
  let cF: class F
  let cG: class G
  let vk: setvar k
  assume stoweidlem33.1: |- F/_ t F
  assume stoweidlem33.2: |- F/_ t G
  assume stoweidlem33.3: |- F/ t ph
  assume stoweidlem33.4: |- ( ( ph /\ f e. A ) -> f : T --> RR )
  assume stoweidlem33.5: |- ( ( ph /\ f e. A /\ g e. A ) -> ( t e. T |-> ( ( f ` t ) + ( g ` t ) ) ) e. A )
  assume stoweidlem33.6: |- ( ( ph /\ f e. A /\ g e. A ) -> ( t e. T |-> ( ( f ` t ) x. ( g ` t ) ) ) e. A )
  assume stoweidlem33.7: |- ( ( ph /\ x e. RR ) -> ( t e. T |-> x ) e. A )

  disjoint f g
  disjoint f t
  disjoint A f
  disjoint g t
  disjoint A g
  disjoint A t
  disjoint F f
  disjoint F g
  disjoint G f
  disjoint G g
  disjoint T f
  disjoint T g
  disjoint T t
  disjoint f ph
  disjoint g ph
  disjoint t x
  disjoint A x
  disjoint T x
  disjoint ph x
  disjoint k x
  assert |- ( ( ph /\ F e. A /\ G e. A ) -> ( t e. T |-> ( ( F ` t ) - ( G ` t ) ) ) e. A )

  proof
    wph
    vx
    vt
    cA
    cT
    vf
    vg
    cF
    cG
    vt
    cT
    vt
    cv
    #
    cF
    cfv
    @0
    cG
    cfv
    #
    cmin
    co
    cmpt
    #
    vt
    cT
    c1
    cneg
    cmpt
    #
    vt
    cT
    @0
    @3
    cfv
    @1
    cmul
    co
    cmpt
    #
    stoweidlem33.3
    stoweidlem33.1
    stoweidlem33.2
    @2
    eqid
    @3
    eqid
    @4
    eqid
    stoweidlem33.4
    stoweidlem33.5
    stoweidlem33.6
    stoweidlem33.7
    stoweidlem22
end
