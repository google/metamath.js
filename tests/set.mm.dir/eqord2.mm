include "wcel.mm"
include "wa.mm"
include "wceq.mm"
include "cneg.mm"
include "cv.mm"
include "negeqd.mm"
include "renegcld.mm"
include "clt.mm"
include "wbr.mm"
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
include "eqord1.mm"
include "recnd.mm"
include "neg11ad.mm"
include "bitrd.mm"

theorem eqord2
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
  assert |- ( ( ph /\ ( C e. S /\ D e. S ) ) -> ( C = D <-> M = N ) )

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
    wceq
    cM
    cneg
    #
    cN
    cneg
    #
    wceq
    cM
    cN
    wceq
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
    @7
    cC
    wceq
    #
    cA
    cM
    ltord.2
    negeqd
    @7
    cD
    wceq
    #
    cA
    cN
    ltord.3
    negeqd
    ltord.4
    wph
    @7
    cS
    wcel
    #
    wa
    cA
    ltord.5
    renegcld
    wph
    @12
    @8
    cS
    wcel
    #
    wa
    wa
    #
    @7
    @8
    clt
    wbr
    cB
    cA
    clt
    wbr
    #
    @5
    @6
    clt
    wbr
    #
    ltord2.6
    @14
    cB
    cr
    wcel
    #
    cA
    cr
    wcel
    #
    @15
    @16
    wb
    wph
    @13
    @17
    @12
    wph
    @18
    vx
    cS
    wral
    #
    @13
    @17
    wph
    @18
    vx
    cS
    ltord.5
    ralrimiva
    #
    @18
    @17
    vx
    @8
    cS
    @9
    cA
    cB
    cr
    ltord.1
    eleq1d
    rspccva
    sylan
    adantrl
    wph
    @12
    @18
    @13
    ltord.5
    adantrr
    cB
    cA
    ltneg
    syl2anc
    sylibd
    eqord1
    @2
    cM
    cN
    @2
    cM
    wph
    @0
    cM
    cr
    wcel
    #
    @1
    wph
    @19
    @0
    @21
    @20
    @18
    @21
    vx
    cC
    cS
    @10
    cA
    cM
    cr
    ltord.2
    eleq1d
    rspccva
    sylan
    adantrr
    recnd
    @2
    cN
    wph
    @1
    cN
    cr
    wcel
    #
    @0
    wph
    @19
    @1
    @22
    @20
    @18
    @22
    vx
    cD
    cS
    @11
    cA
    cN
    cr
    ltord.3
    eleq1d
    rspccva
    sylan
    adantrl
    recnd
    neg11ad
    bitrd
end
