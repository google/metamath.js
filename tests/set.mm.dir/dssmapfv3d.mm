include "cfv.mm"
include "cdif.mm"
include "cv.mm"
include "cpw.mm"
include "cvv.mm"
include "dssmapfv2d.mm"
include "wceq.mm"
include "difeq2.mm"
include "fveq2d.mm"
include "difeq2d.mm"
include "adantl.mm"
include "wcel.mm"
include "difexg.mm"
include "syl.mm"
include "fvmptd.mm"
include "syl5eq.mm"

theorem dssmapfv3d
  let wph: wff ph
  let cB: class B
  let cD: class D
  let cS: class S
  let cT: class T
  let vf: setvar f
  let cF: class F
  let cG: class G
  let cO: class O
  let cV: class V
  let vs: setvar s
  let vb: setvar b
  assume dssmapfvd.o: |- O = ( b e. _V |-> ( f e. ( ~P b ^m ~P b ) |-> ( s e. ~P b |-> ( b \ ( f ` ( b \ s ) ) ) ) ) )
  assume dssmapfvd.d: |- D = ( O ` B )
  assume dssmapfvd.b: |- ( ph -> B e. V )
  assume dssmapfv2d.f: |- ( ph -> F e. ( ~P B ^m ~P B ) )
  assume dssmapfv2d.g: |- G = ( D ` F )
  assume dssmapfv3d.s: |- ( ph -> S e. ~P B )
  assume dssmapfv3d.t: |- T = ( G ` S )

  disjoint B b
  disjoint B f
  disjoint B s
  disjoint b f
  disjoint b s
  disjoint f s
  disjoint F f
  disjoint F s
  disjoint S s
  disjoint b ph
  disjoint f ph
  disjoint ph s
  assert |- ( ph -> T = ( B \ ( F ` ( B \ S ) ) ) )

  proof
    wph
    cT
    cS
    cG
    cfv
    cB
    cB
    cS
    cdif
    #
    cF
    cfv
    #
    cdif
    #
    dssmapfv3d.t
    wph
    vs
    cS
    cB
    cB
    vs
    cv
    #
    cdif
    #
    cF
    cfv
    #
    cdif
    #
    @2
    cB
    cpw
    cG
    cvv
    wph
    cB
    cD
    vf
    cF
    cG
    cO
    cV
    vs
    vb
    dssmapfvd.o
    dssmapfvd.d
    dssmapfvd.b
    dssmapfv2d.f
    dssmapfv2d.g
    dssmapfv2d
    @3
    cS
    wceq
    #
    @6
    @2
    wceq
    wph
    @7
    @5
    @1
    cB
    @7
    @4
    @0
    cF
    @3
    cS
    cB
    difeq2
    fveq2d
    difeq2d
    adantl
    dssmapfv3d.s
    wph
    cB
    cV
    wcel
    @2
    cvv
    wcel
    dssmapfvd.b
    cB
    @1
    cV
    difexg
    syl
    fvmptd
    syl5eq
end
