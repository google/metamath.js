include "cfv.mm"
include "cpw.mm"
include "cv.mm"
include "cdif.mm"
include "cmpt.mm"
include "cmap.mm"
include "co.mm"
include "cvv.mm"
include "dssmapfvd.mm"
include "wceq.mm"
include "fveq1.mm"
include "difeq2d.mm"
include "mpteq2dv.mm"
include "adantl.mm"
include "wcel.mm"
include "pwexg.mm"
include "mptexg.mm"
include "3syl.mm"
include "fvmptd.mm"
include "syl5eq.mm"

theorem dssmapfv2d
  let wph: wff ph
  let cB: class B
  let cD: class D
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

  disjoint B b
  disjoint B f
  disjoint B s
  disjoint b f
  disjoint b s
  disjoint f s
  disjoint F f
  disjoint F s
  disjoint b ph
  disjoint f ph
  assert |- ( ph -> G = ( s e. ~P B |-> ( B \ ( F ` ( B \ s ) ) ) ) )

  proof
    wph
    cG
    cF
    cD
    cfv
    vs
    cB
    cpw
    #
    cB
    cB
    vs
    cv
    cdif
    #
    cF
    cfv
    #
    cdif
    #
    cmpt
    #
    dssmapfv2d.g
    wph
    vf
    cF
    vs
    @0
    cB
    @1
    vf
    cv
    #
    cfv
    #
    cdif
    #
    cmpt
    #
    @4
    @0
    @0
    cmap
    co
    cD
    cvv
    wph
    cB
    cD
    vf
    cO
    cV
    vs
    vb
    dssmapfvd.o
    dssmapfvd.d
    dssmapfvd.b
    dssmapfvd
    @5
    cF
    wceq
    #
    @8
    @4
    wceq
    wph
    @9
    vs
    @0
    @7
    @3
    @9
    @6
    @2
    cB
    @1
    @5
    cF
    fveq1
    difeq2d
    mpteq2dv
    adantl
    dssmapfv2d.f
    wph
    cB
    cV
    wcel
    @0
    cvv
    wcel
    @4
    cvv
    wcel
    dssmapfvd.b
    cB
    cV
    pwexg
    vs
    @0
    @3
    cvv
    mptexg
    3syl
    fvmptd
    syl5eq
end
