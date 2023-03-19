include "cv.mm"
include "crn.mm"
include "wcel.mm"
include "cpr.mm"
include "wb.mm"
include "wal.mm"
include "wceq.mm"
include "wrex.mm"
include "wo.mm"
include "cvv.mm"
include "vex.mm"
include "elrnmpt.mm"
include "ax-mp.mm"
include "a1i.mm"
include "eqeq2d.mm"
include "rexprg.mm"
include "syl2anc.mm"
include "elpr.mm"
include "bicomi.mm"
include "3bitrd.mm"
include "alrimiv.mm"
include "dfcleq.mm"
include "sylibr.mm"

theorem rnmptpr
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cE: class E
  let cF: class F
  let cV: class V
  let cW: class W
  let vy: setvar y
  assume rnmptpr.a: |- ( ph -> A e. V )
  assume rnmptpr.b: |- ( ph -> B e. W )
  assume rnmptpr.f: |- F = ( x e. { A , B } |-> C )
  assume rnmptpr.d: |- ( x = A -> C = D )
  assume rnmptpr.e: |- ( x = B -> C = E )

  disjoint A x
  disjoint B x
  disjoint D x
  disjoint E x
  disjoint D y
  disjoint x y
  disjoint E y
  disjoint F y
  disjoint ph y
  assert |- ( ph -> ran F = { D , E } )

  proof
    wph
    vy
    cv
    #
    cF
    crn
    #
    wcel
    #
    @0
    cD
    cE
    cpr
    #
    wcel
    #
    wb
    #
    vy
    wal
    @1
    @3
    wceq
    wph
    @5
    vy
    wph
    @2
    @0
    cC
    wceq
    #
    vx
    cA
    cB
    cpr
    #
    wrex
    #
    @0
    cD
    wceq
    #
    @0
    cE
    wceq
    #
    wo
    #
    @4
    @2
    @8
    wb
    #
    wph
    @0
    cvv
    wcel
    @12
    vy
    vex
    #
    vx
    @7
    cC
    @0
    cF
    cvv
    rnmptpr.f
    elrnmpt
    ax-mp
    a1i
    wph
    cA
    cV
    wcel
    cB
    cW
    wcel
    @8
    @11
    wb
    rnmptpr.a
    rnmptpr.b
    @6
    @9
    @10
    vx
    cA
    cB
    cV
    cW
    vx
    cv
    #
    cA
    wceq
    cC
    cD
    @0
    rnmptpr.d
    eqeq2d
    @14
    cB
    wceq
    cC
    cE
    @0
    rnmptpr.e
    eqeq2d
    rexprg
    syl2anc
    @11
    @4
    wb
    wph
    @4
    @11
    @0
    cD
    cE
    @13
    elpr
    bicomi
    a1i
    3bitrd
    alrimiv
    vy
    @1
    @3
    dfcleq
    sylibr
end
