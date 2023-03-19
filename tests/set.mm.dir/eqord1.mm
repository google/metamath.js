include "wcel.mm"
include "wa.mm"
include "cle.mm"
include "wbr.mm"
include "wceq.mm"
include "leord1.mm"
include "wb.mm"
include "ancom2s.mm"
include "anbi12d.mm"
include "cr.mm"
include "sseli.mm"
include "letri3.mm"
include "syl2an.mm"
include "adantl.mm"
include "wral.mm"
include "ralrimiva.mm"
include "cv.mm"
include "eleq1d.mm"
include "rspccva.mm"
include "sylan.mm"
include "adantrr.mm"
include "adantrl.mm"
include "letri3d.mm"
include "3bitr4d.mm"

theorem eqord1
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
  assume ltord.6: |- ( ( ph /\ ( x e. S /\ y e. S ) ) -> ( x < y -> A < B ) )

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
    #
    wa
    #
    cC
    cD
    cle
    wbr
    #
    cD
    cC
    cle
    wbr
    #
    wa
    #
    cM
    cN
    cle
    wbr
    #
    cN
    cM
    cle
    wbr
    #
    wa
    cC
    cD
    wceq
    #
    cM
    cN
    wceq
    @3
    @4
    @7
    @5
    @8
    wph
    vx
    vy
    cA
    cB
    cC
    cD
    cS
    cM
    cN
    ltord.1
    ltord.2
    ltord.3
    ltord.4
    ltord.5
    ltord.6
    leord1
    wph
    @1
    @0
    @5
    @8
    wb
    wph
    vx
    vy
    cA
    cB
    cD
    cC
    cS
    cN
    cM
    ltord.1
    ltord.3
    ltord.2
    ltord.4
    ltord.5
    ltord.6
    leord1
    ancom2s
    anbi12d
    @2
    @9
    @6
    wb
    #
    wph
    @0
    cC
    cr
    wcel
    cD
    cr
    wcel
    @10
    @1
    cS
    cr
    cC
    ltord.4
    sseli
    cS
    cr
    cD
    ltord.4
    sseli
    cC
    cD
    letri3
    syl2an
    adantl
    @3
    cM
    cN
    wph
    @0
    cM
    cr
    wcel
    #
    @1
    wph
    cA
    cr
    wcel
    #
    vx
    cS
    wral
    #
    @0
    @11
    wph
    @12
    vx
    cS
    ltord.5
    ralrimiva
    #
    @12
    @11
    vx
    cC
    cS
    vx
    cv
    #
    cC
    wceq
    cA
    cM
    cr
    ltord.2
    eleq1d
    rspccva
    sylan
    adantrr
    wph
    @1
    cN
    cr
    wcel
    #
    @0
    wph
    @13
    @1
    @16
    @14
    @12
    @16
    vx
    cD
    cS
    @15
    cD
    wceq
    cA
    cN
    cr
    ltord.3
    eleq1d
    rspccva
    sylan
    adantrl
    letri3d
    3bitr4d
end
