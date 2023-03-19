include "ccnv.mm"
include "cvv.mm"
include "cv.mm"
include "cplusg.mm"
include "cfv.mm"
include "co.mm"
include "wceq.mm"
include "wa.mm"
include "cbs.mm"
include "wral.mm"
include "crab.mm"
include "cdif.mm"
include "cima.mm"
include "eqid.mm"
include "gsumpropd2lem.mm"

theorem gsumpropd2
  let wph: wff ph
  let vt: setvar t
  let cF: class F
  let cG: class G
  let cH: class H
  let cV: class V
  let cW: class W
  let cX: class X
  let vs: setvar s
  let va: setvar a
  let vb: setvar b
  let cA: class A
  let cB: class B
  let vf: setvar f
  let vm: setvar m
  let vn: setvar n
  let vx: setvar x
  assume gsumpropd2.f: |- ( ph -> F e. V )
  assume gsumpropd2.g: |- ( ph -> G e. W )
  assume gsumpropd2.h: |- ( ph -> H e. X )
  assume gsumpropd2.b: |- ( ph -> ( Base ` G ) = ( Base ` H ) )
  assume gsumpropd2.c: |- ( ( ph /\ ( s e. ( Base ` G ) /\ t e. ( Base ` G ) ) ) -> ( s ( +g ` G ) t ) e. ( Base ` G ) )
  assume gsumpropd2.e: |- ( ( ph /\ ( s e. ( Base ` G ) /\ t e. ( Base ` G ) ) ) -> ( s ( +g ` G ) t ) = ( s ( +g ` H ) t ) )
  assume gsumpropd2.n: |- ( ph -> Fun F )
  assume gsumpropd2.r: |- ( ph -> ran F C_ ( Base ` G ) )

  disjoint s t
  disjoint F s
  disjoint F t
  disjoint G s
  disjoint G t
  disjoint H s
  disjoint H t
  disjoint ph s
  disjoint ph t
  disjoint a b
  disjoint A a
  disjoint A b
  disjoint B a
  disjoint B b
  disjoint a f
  disjoint a m
  disjoint a n
  disjoint a s
  disjoint a t
  disjoint a x
  disjoint F a
  disjoint b f
  disjoint b m
  disjoint b n
  disjoint b s
  disjoint b t
  disjoint b x
  disjoint F b
  disjoint f m
  disjoint f n
  disjoint f s
  disjoint f t
  disjoint f x
  disjoint F f
  disjoint m n
  disjoint m s
  disjoint m t
  disjoint m x
  disjoint F m
  disjoint n s
  disjoint n t
  disjoint n x
  disjoint F n
  disjoint s x
  disjoint t x
  disjoint F x
  disjoint G a
  disjoint G b
  disjoint G f
  disjoint G m
  disjoint G n
  disjoint G x
  disjoint H a
  disjoint H b
  disjoint H f
  disjoint H m
  disjoint H n
  disjoint H x
  disjoint a ph
  disjoint b ph
  disjoint f ph
  disjoint m ph
  disjoint n ph
  disjoint ph x
  assert |- ( ph -> ( G gsum F ) = ( H gsum F ) )

  proof
    wph
    vt
    cF
    ccnv
    #
    cvv
    vs
    cv
    #
    vt
    cv
    #
    cG
    cplusg
    cfv
    #
    co
    @2
    wceq
    @2
    @1
    @3
    co
    @2
    wceq
    wa
    vt
    cG
    cbs
    cfv
    #
    wral
    vs
    @4
    crab
    cdif
    cima
    #
    @0
    cvv
    @1
    @2
    cH
    cplusg
    cfv
    #
    co
    @2
    wceq
    @2
    @1
    @6
    co
    @2
    wceq
    wa
    vt
    cH
    cbs
    cfv
    #
    wral
    vs
    @7
    crab
    cdif
    cima
    #
    cF
    cG
    cH
    cV
    cW
    cX
    vs
    gsumpropd2.f
    gsumpropd2.g
    gsumpropd2.h
    gsumpropd2.b
    gsumpropd2.c
    gsumpropd2.e
    gsumpropd2.n
    gsumpropd2.r
    @5
    eqid
    @8
    eqid
    gsumpropd2lem
end
