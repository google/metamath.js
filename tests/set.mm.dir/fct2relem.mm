include "cicc.mm"
include "co.mm"
include "cioo.mm"
include "cxr.mm"
include "wcel.mm"
include "clt.mm"
include "wbr.mm"
include "wss.mm"
include "wa.mm"
include "syl6eleq.mm"
include "eliooxr.mm"
include "syl.mm"
include "simpld.mm"
include "simprd.mm"
include "eliooord.mm"
include "iccssioo.mm"
include "syl22anc.mm"
include "syl6sseqr.mm"

theorem fct2relem
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cE: class E
  let vt: setvar t
  let vx: setvar x
  let vy: setvar y
  let cF: class F
  assume ftc2re.e: |- E = ( C (,) D )
  assume ftc2re.a: |- ( ph -> A e. E )
  assume ftc2re.b: |- ( ph -> B e. E )


  assert |- ( ph -> ( A [,] B ) C_ E )

  proof
    wph
    cA
    cB
    cicc
    co
    #
    cC
    cD
    cioo
    co
    #
    cE
    wph
    cC
    cxr
    wcel
    #
    cD
    cxr
    wcel
    #
    cC
    cA
    clt
    wbr
    #
    cB
    cD
    clt
    wbr
    #
    @0
    @1
    wss
    wph
    @2
    @3
    wph
    cA
    @1
    wcel
    #
    @2
    @3
    wa
    wph
    cA
    cE
    @1
    ftc2re.a
    ftc2re.e
    syl6eleq
    #
    cA
    cC
    cD
    eliooxr
    syl
    #
    simpld
    wph
    @2
    @3
    @8
    simprd
    wph
    @4
    cA
    cD
    clt
    wbr
    #
    wph
    @6
    @4
    @9
    wa
    @7
    cA
    cC
    cD
    eliooord
    syl
    simpld
    wph
    cC
    cB
    clt
    wbr
    #
    @5
    wph
    cB
    @1
    wcel
    @10
    @5
    wa
    wph
    cB
    cE
    @1
    ftc2re.b
    ftc2re.e
    syl6eleq
    cB
    cC
    cD
    eliooord
    syl
    simprd
    cC
    cD
    cA
    cB
    iccssioo
    syl22anc
    ftc2re.e
    syl6sseqr
end
