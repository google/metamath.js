include "cv.mm"
include "cc0.mm"
include "c2.mm"
include "cfzo.mm"
include "co.mm"
include "wcel.mm"
include "wa.mm"
include "wceq.mm"
include "cs2.mm"
include "cfv.mm"
include "chash.mm"
include "c1.mm"
include "simpr.mm"
include "fveq2d.mm"
include "cword.mm"
include "s2cld.mm"
include "s2fv0.mm"
include "syl.mm"
include "adantr.mm"
include "eqtrd.mm"
include "s2len.mm"
include "syl6eq.mm"
include "adantlr.mm"
include "s2fv1.mm"
include "wo.mm"
include "cpr.mm"
include "fzo0to2pr.mm"
include "eleq2i.mm"
include "vex.mm"
include "elpr.mm"
include "bitri.mm"
include "biimpi.mm"
include "adantl.mm"
include "mpjaodan.mm"

theorem lmat22lem
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let vi: setvar i
  let cM: class M
  let cV: class V
  assume lmat22.m: |- M = ( litMat ` <" <" A B "> <" C D "> "> )
  assume lmat22.a: |- ( ph -> A e. V )
  assume lmat22.b: |- ( ph -> B e. V )
  assume lmat22.c: |- ( ph -> C e. V )
  assume lmat22.d: |- ( ph -> D e. V )

  disjoint A i
  disjoint B i
  disjoint C i
  disjoint D i
  disjoint M i
  disjoint i ph
  assert |- ( ( ph /\ i e. ( 0 ..^ 2 ) ) -> ( # ` ( <" <" A B "> <" C D "> "> ` i ) ) = 2 )

  proof
    wph
    vi
    cv
    #
    cc0
    c2
    cfzo
    co
    #
    wcel
    #
    wa
    @0
    cc0
    wceq
    #
    @0
    cA
    cB
    cs2
    #
    cC
    cD
    cs2
    #
    cs2
    #
    cfv
    #
    chash
    cfv
    #
    c2
    wceq
    #
    @0
    c1
    wceq
    #
    wph
    @3
    @9
    @2
    wph
    @3
    wa
    #
    @8
    @4
    chash
    cfv
    c2
    @11
    @7
    @4
    chash
    @11
    @7
    cc0
    @6
    cfv
    #
    @4
    @11
    @0
    cc0
    @6
    wph
    @3
    simpr
    fveq2d
    wph
    @12
    @4
    wceq
    #
    @3
    wph
    @4
    cV
    cword
    #
    wcel
    @13
    wph
    cA
    cB
    cV
    lmat22.a
    lmat22.b
    s2cld
    @4
    @5
    @14
    s2fv0
    syl
    adantr
    eqtrd
    fveq2d
    cA
    cB
    s2len
    syl6eq
    adantlr
    wph
    @10
    @9
    @2
    wph
    @10
    wa
    #
    @8
    @5
    chash
    cfv
    c2
    @15
    @7
    @5
    chash
    @15
    @7
    c1
    @6
    cfv
    #
    @5
    @15
    @0
    c1
    @6
    wph
    @10
    simpr
    fveq2d
    wph
    @16
    @5
    wceq
    #
    @10
    wph
    @5
    @14
    wcel
    @17
    wph
    cC
    cD
    cV
    lmat22.c
    lmat22.d
    s2cld
    @4
    @5
    @14
    s2fv1
    syl
    adantr
    eqtrd
    fveq2d
    cC
    cD
    s2len
    syl6eq
    adantlr
    @2
    @3
    @10
    wo
    #
    wph
    @2
    @18
    @2
    @0
    cc0
    c1
    cpr
    #
    wcel
    @18
    @1
    @19
    @0
    fzo0to2pr
    eleq2i
    @0
    cc0
    c1
    vi
    vex
    elpr
    bitri
    biimpi
    adantl
    mpjaodan
end
