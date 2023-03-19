include "cqs.mm"
include "wcel.mm"
include "wceq.mm"
include "cin.mm"
include "c0.mm"
include "wo.mm"
include "cv.mm"
include "cec.mm"
include "eqid.mm"
include "eqeq1.mm"
include "ineq1.mm"
include "eqeq1d.mm"
include "orbi12d.mm"
include "wa.mm"
include "eqeq2.mm"
include "ineq2.mm"
include "wer.mm"
include "ad2antrr.mm"
include "erdisj.mm"
include "syl.mm"
include "ectocld.mm"
include "mpidan.mm"
include "mpdan.mm"

theorem qsdisj
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cR: class R
  let cX: class X
  let vx: setvar x
  let vy: setvar y
  assume qsdisj.1: |- ( ph -> R Er X )
  assume qsdisj.2: |- ( ph -> B e. ( A /. R ) )
  assume qsdisj.3: |- ( ph -> C e. ( A /. R ) )


  assert |- ( ph -> ( B = C \/ ( B i^i C ) = (/) ) )

  proof
    wph
    cB
    cA
    cR
    cqs
    #
    wcel
    cB
    cC
    wceq
    #
    cB
    cC
    cin
    #
    c0
    wceq
    #
    wo
    #
    qsdisj.2
    vx
    cv
    #
    cR
    cec
    #
    cC
    wceq
    #
    @6
    cC
    cin
    #
    c0
    wceq
    #
    wo
    #
    @4
    wph
    vx
    cB
    cA
    cR
    @0
    @0
    eqid
    #
    @6
    cB
    wceq
    #
    @7
    @1
    @9
    @3
    @6
    cB
    cC
    eqeq1
    @12
    @8
    @2
    c0
    @6
    cB
    cC
    ineq1
    eqeq1d
    orbi12d
    wph
    @5
    cA
    wcel
    #
    cC
    @0
    wcel
    @10
    qsdisj.3
    @6
    vy
    cv
    #
    cR
    cec
    #
    wceq
    #
    @6
    @15
    cin
    #
    c0
    wceq
    #
    wo
    #
    @10
    wph
    @13
    wa
    #
    vy
    cC
    cA
    cR
    @0
    @11
    @15
    cC
    wceq
    #
    @16
    @7
    @18
    @9
    @15
    cC
    @6
    eqeq2
    @21
    @17
    @8
    c0
    @15
    cC
    @6
    ineq2
    eqeq1d
    orbi12d
    @20
    @14
    cA
    wcel
    #
    wa
    cX
    cR
    wer
    #
    @19
    wph
    @23
    @13
    @22
    qsdisj.1
    ad2antrr
    @5
    @14
    cR
    cX
    erdisj
    syl
    ectocld
    mpidan
    ectocld
    mpdan
end
