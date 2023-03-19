include "wceq.mm"
include "cv.mm"
include "cfv.mm"
include "wral.mm"
include "wfn.mm"
include "wb.mm"
include "eqfnfv.mm"
include "syl2anc.mm"
include "wa.mm"
include "wcel.mm"
include "csn.mm"
include "snidg.mm"
include "syl.mm"
include "eqcomi.mm"
include "a1i.mm"
include "eleqtrd.mm"
include "adantr.mm"
include "simpr.mm"
include "fveq2.mm"
include "eqeq12d.mm"
include "rspcva.mm"
include "ex.mm"
include "simpl.mm"
include "eleq2i.mm"
include "biimpi.mm"
include "velsn.mm"
include "sylib.mm"
include "fveq2d.mm"
include "adantl.mm"
include "3eqtr4d.mm"
include "adantll.mm"
include "ralrimiva.mm"
include "impbid.mm"
include "bitrd.mm"

theorem fsneq
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cF: class F
  let cG: class G
  let cV: class V
  let vx: setvar x
  assume fsneq.a: |- ( ph -> A e. V )
  assume fsneq.b: |- B = { A }
  assume fsneq.f: |- ( ph -> F Fn B )
  assume fsneq.g: |- ( ph -> G Fn B )


  assert |- ( ph -> ( F = G <-> ( F ` A ) = ( G ` A ) ) )

  proof
    wph
    cF
    cG
    wceq
    #
    vx
    cv
    #
    cF
    cfv
    #
    @1
    cG
    cfv
    #
    wceq
    #
    vx
    cB
    wral
    #
    cA
    cF
    cfv
    #
    cA
    cG
    cfv
    #
    wceq
    #
    wph
    cF
    cB
    wfn
    cG
    cB
    wfn
    @0
    @5
    wb
    fsneq.f
    fsneq.g
    vx
    cB
    cF
    cG
    eqfnfv
    syl2anc
    wph
    @5
    @8
    wph
    @5
    @8
    wph
    @5
    wa
    cA
    cB
    wcel
    #
    @5
    @8
    wph
    @9
    @5
    wph
    cA
    cA
    csn
    #
    cB
    wph
    cA
    cV
    wcel
    cA
    @10
    wcel
    fsneq.a
    cA
    cV
    snidg
    syl
    @10
    cB
    wceq
    wph
    cB
    @10
    fsneq.b
    eqcomi
    a1i
    eleqtrd
    adantr
    wph
    @5
    simpr
    @4
    @8
    vx
    cA
    cB
    @1
    cA
    wceq
    #
    @2
    @6
    @3
    @7
    @1
    cA
    cF
    fveq2
    @1
    cA
    cG
    fveq2
    eqeq12d
    rspcva
    syl2anc
    ex
    wph
    @8
    @5
    wph
    @8
    wa
    @4
    vx
    cB
    @8
    @1
    cB
    wcel
    #
    @4
    wph
    @8
    @12
    wa
    @6
    @7
    @2
    @3
    @8
    @12
    simpl
    @12
    @2
    @6
    wceq
    @8
    @12
    @1
    cA
    cF
    @12
    @1
    @10
    wcel
    #
    @11
    @12
    @13
    cB
    @10
    @1
    fsneq.b
    eleq2i
    biimpi
    vx
    cA
    velsn
    sylib
    #
    fveq2d
    adantl
    @12
    @3
    @7
    wceq
    @8
    @12
    @1
    cA
    cG
    @14
    fveq2d
    adantl
    3eqtr4d
    adantll
    ralrimiva
    ex
    impbid
    bitrd
end
