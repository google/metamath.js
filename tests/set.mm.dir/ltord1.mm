include "wcel.mm"
include "wa.mm"
include "clt.mm"
include "wbr.mm"
include "ltordlem.mm"
include "wceq.mm"
include "wo.mm"
include "wn.mm"
include "wi.mm"
include "cv.mm"
include "eqeq1.mm"
include "eqeq1d.mm"
include "imbi12d.mm"
include "vtoclg.mm"
include "ad2antrl.mm"
include "ancom2s.mm"
include "orim12d.mm"
include "con3d.mm"
include "cr.mm"
include "wb.mm"
include "wral.mm"
include "ralrimiva.mm"
include "eleq1d.mm"
include "rspccva.mm"
include "sylan.mm"
include "anim12dan.mm"
include "axlttri.mm"
include "syl.mm"
include "sseli.mm"
include "syl2an.mm"
include "adantl.mm"
include "3imtr4d.mm"
include "impbid.mm"

theorem ltord1
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
  assert |- ( ( ph /\ ( C e. S /\ D e. S ) ) -> ( C < D <-> M < N ) )

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
    clt
    wbr
    #
    cM
    cN
    clt
    wbr
    #
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
    ltordlem
    @3
    cM
    cN
    wceq
    #
    cN
    cM
    clt
    wbr
    #
    wo
    #
    wn
    #
    cC
    cD
    wceq
    #
    cD
    cC
    clt
    wbr
    #
    wo
    #
    wn
    #
    @5
    @4
    @3
    @12
    @8
    @3
    @10
    @6
    @11
    @7
    @0
    @10
    @6
    wi
    #
    wph
    @1
    vx
    cv
    #
    cD
    wceq
    #
    cA
    cN
    wceq
    #
    wi
    @14
    vx
    cC
    cS
    @15
    cC
    wceq
    #
    @16
    @10
    @17
    @6
    @15
    cC
    cD
    eqeq1
    @18
    cA
    cM
    cN
    ltord.2
    eqeq1d
    imbi12d
    ltord.3
    vtoclg
    ad2antrl
    wph
    @1
    @0
    @11
    @7
    wi
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
    ltordlem
    ancom2s
    orim12d
    con3d
    @3
    cM
    cr
    wcel
    #
    cN
    cr
    wcel
    #
    wa
    @5
    @9
    wb
    wph
    @0
    @19
    @1
    @20
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
    @19
    wph
    @21
    vx
    cS
    ltord.5
    ralrimiva
    #
    @21
    @19
    vx
    cC
    cS
    @18
    cA
    cM
    cr
    ltord.2
    eleq1d
    rspccva
    sylan
    wph
    @22
    @1
    @20
    @23
    @21
    @20
    vx
    cD
    cS
    @16
    cA
    cN
    cr
    ltord.3
    eleq1d
    rspccva
    sylan
    anim12dan
    cM
    cN
    axlttri
    syl
    @2
    @4
    @13
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
    @24
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
    axlttri
    syl2an
    adantl
    3imtr4d
    impbid
end
