include "wcel.mm"
include "wa.mm"
include "cle.mm"
include "wbr.mm"
include "cneg.mm"
include "cv.mm"
include "wceq.mm"
include "negeqd.mm"
include "renegcld.mm"
include "clt.mm"
include "cr.mm"
include "wb.mm"
include "wral.mm"
include "ralrimiva.mm"
include "eleq1d.mm"
include "rspccva.mm"
include "sylan.mm"
include "adantrl.mm"
include "adantrr.mm"
include "ltneg.mm"
include "syl2anc.mm"
include "sylibd.mm"
include "leord1.mm"
include "leneg.mm"
include "bitr4d.mm"

theorem leord2
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cS: class S
  let cM: class M
  let cN: class N
  assume ltord.1: |- ( x = y -> A = B )
  assume ltord.2: |- ( x = C -> A = M )
  assume ltord.3: |- ( x = D -> A = N )
  assume ltord.4: |- S C_ RR
  assume ltord.5: |- ( ( ph /\ x e. S ) -> A e. RR )
  assume ltord2.6: |- ( ( ph /\ ( x e. S /\ y e. S ) ) -> ( x < y -> B < A ) )

  disjoint B x
  disjoint x y
  disjoint C x
  disjoint C y
  disjoint D x
  disjoint D y
  disjoint M x
  disjoint M y
  disjoint N x
  disjoint N y
  disjoint ph x
  disjoint ph y
  disjoint S x
  disjoint S y
  assert |- ( ( ph /\ ( C e. S /\ D e. S ) ) -> ( C <_ D <-> N <_ M ) )

  proof
    wph
    cC
    cS
    wcel
    #
    cD
    cS
    wcel
    #
    wa
    wa
    #
    cC
    cD
    cle
    wbr
    cM
    cneg
    #
    cN
    cneg
    #
    cle
    wbr
    #
    cN
    cM
    cle
    wbr
    #
    wph
    vx
    vy
    cA
    cneg
    #
    cB
    cneg
    #
    cC
    cD
    cS
    @3
    @4
    vx
    cv
    #
    vy
    cv
    #
    wceq
    #
    cA
    cB
    ltord.1
    negeqd
    @9
    cC
    wceq
    #
    cA
    cM
    ltord.2
    negeqd
    @9
    cD
    wceq
    #
    cA
    cN
    ltord.3
    negeqd
    ltord.4
    wph
    @9
    cS
    wcel
    #
    wa
    cA
    ltord.5
    renegcld
    wph
    @14
    @10
    cS
    wcel
    #
    wa
    wa
    #
    @9
    @10
    clt
    wbr
    cB
    cA
    clt
    wbr
    #
    @7
    @8
    clt
    wbr
    #
    ltord2.6
    @16
    cB
    cr
    wcel
    #
    cA
    cr
    wcel
    #
    @17
    @18
    wb
    wph
    @15
    @19
    @14
    wph
    @20
    vx
    cS
    wral
    #
    @15
    @19
    wph
    @20
    vx
    cS
    ltord.5
    ralrimiva
    #
    @20
    @19
    vx
    @10
    cS
    @11
    cA
    cB
    cr
    ltord.1
    eleq1d
    rspccva
    sylan
    adantrl
    wph
    @14
    @20
    @15
    ltord.5
    adantrr
    cB
    cA
    ltneg
    syl2anc
    sylibd
    leord1
    @2
    cN
    cr
    wcel
    #
    cM
    cr
    wcel
    #
    @6
    @5
    wb
    wph
    @1
    @23
    @0
    wph
    @21
    @1
    @23
    @22
    @20
    @23
    vx
    cD
    cS
    @13
    cA
    cN
    cr
    ltord.3
    eleq1d
    rspccva
    sylan
    adantrl
    wph
    @0
    @24
    @1
    wph
    @21
    @0
    @24
    @22
    @20
    @24
    vx
    cC
    cS
    @12
    cA
    cM
    cr
    ltord.2
    eleq1d
    rspccva
    sylan
    adantrr
    cN
    cM
    leneg
    syl2anc
    bitr4d
end
