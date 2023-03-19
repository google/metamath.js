include "ccnv.mm"
include "cfv.mm"
include "co.mm"
include "cv.mm"
include "wcel.mm"
include "crab.mm"
include "cmpt.mm"
include "eqid.mm"
include "fsovcnvd.mm"
include "fveq1d.mm"
include "fsovfvd.mm"
include "eqtrd.mm"

theorem fsovcnvfvd
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let vf: setvar f
  let cF: class F
  let cG: class G
  let cO: class O
  let cV: class V
  let cW: class W
  let va: setvar a
  let vb: setvar b
  assume fsovd.fs: |- O = ( a e. _V , b e. _V |-> ( f e. ( ~P b ^m a ) |-> ( y e. b |-> { x e. a | y e. ( f ` x ) } ) ) )
  assume fsovd.a: |- ( ph -> A e. V )
  assume fsovd.b: |- ( ph -> B e. W )
  assume fsovfvd.g: |- G = ( A O B )
  assume fsovcnvfvd.f: |- ( ph -> F e. ( ~P A ^m B ) )

  disjoint A a
  disjoint A b
  disjoint A f
  disjoint A x
  disjoint A y
  disjoint a b
  disjoint a f
  disjoint a x
  disjoint a y
  disjoint b f
  disjoint b x
  disjoint b y
  disjoint f x
  disjoint f y
  disjoint x y
  disjoint B a
  disjoint B b
  disjoint B f
  disjoint B x
  disjoint B y
  disjoint F f
  disjoint F x
  disjoint F y
  disjoint a ph
  disjoint b ph
  disjoint f ph
  disjoint ph y
  assert |- ( ph -> ( `' G ` F ) = ( y e. A |-> { x e. B | y e. ( F ` x ) } ) )

  proof
    wph
    cF
    cG
    ccnv
    #
    cfv
    cF
    cB
    cA
    cO
    co
    #
    cfv
    vy
    cA
    vy
    cv
    vx
    cv
    cF
    cfv
    wcel
    vx
    cB
    crab
    cmpt
    wph
    cF
    @0
    @1
    wph
    vx
    vy
    cA
    cB
    vf
    cG
    @1
    cO
    cV
    cW
    va
    vb
    fsovd.fs
    fsovd.a
    fsovd.b
    fsovfvd.g
    @1
    eqid
    #
    fsovcnvd
    fveq1d
    wph
    vx
    vy
    cB
    cA
    vf
    cF
    @1
    cO
    cW
    cV
    va
    vb
    fsovd.fs
    fsovd.b
    fsovd.a
    @2
    fsovcnvfvd.f
    fsovfvd
    eqtrd
end
