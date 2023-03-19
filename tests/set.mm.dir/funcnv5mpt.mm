include "ccnv.mm"
include "wfun.mm"
include "cv.mm"
include "wceq.mm"
include "wrmo.mm"
include "wal.mm"
include "wne.mm"
include "wo.mm"
include "wral.mm"
include "funcnvmpt.mm"
include "wa.mm"
include "wi.mm"
include "wcel.mm"
include "wn.mm"
include "wex.mm"
include "nne.mm"
include "wb.mm"
include "eqvincg.mm"
include "syl.mm"
include "syl5bb.mm"
include "imbi1d.mm"
include "orcom.mm"
include "df-or.mm"
include "bitri.mm"
include "19.23v.mm"
include "3bitr4g.mm"
include "ralbidv.mm"
include "ralcom4.mm"
include "syl6bb.mm"
include "ralbida.mm"
include "nfcv.mm"
include "nfv.mm"
include "eqeq2d.mm"
include "rmo4f.mm"
include "albii.mm"
include "bitr4i.mm"
include "syl6bbr.mm"
include "bitr4d.mm"

theorem funcnv5mpt
  let wph: wff ph
  let vx: setvar x
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F
  let cV: class V
  let vy: setvar y
  assume funcnvmpt.0: |- F/ x ph
  assume funcnvmpt.1: |- F/_ x A
  assume funcnvmpt.2: |- F/_ x F
  assume funcnvmpt.3: |- F = ( x e. A |-> B )
  assume funcnvmpt.4: |- ( ( ph /\ x e. A ) -> B e. V )
  assume funcnv5mpt.1: |- ( x = z -> B = C )

  disjoint A z
  disjoint B z
  disjoint C x
  disjoint x z
  disjoint ph z
  disjoint y z
  disjoint A y
  disjoint B y
  disjoint x y
  disjoint C y
  disjoint x y
  disjoint y z
  disjoint F y
  disjoint ph y
  assert |- ( ph -> ( Fun `' F <-> A. x e. A A. z e. A ( x = z \/ B =/= C ) ) )

  proof
    wph
    cF
    ccnv
    wfun
    vy
    cv
    #
    cB
    wceq
    #
    vx
    cA
    wrmo
    #
    vy
    wal
    #
    vx
    cv
    #
    vz
    cv
    wceq
    #
    cB
    cC
    wne
    #
    wo
    #
    vz
    cA
    wral
    #
    vx
    cA
    wral
    #
    wph
    vx
    vy
    cA
    cB
    cF
    cV
    funcnvmpt.0
    funcnvmpt.1
    funcnvmpt.2
    funcnvmpt.3
    funcnvmpt.4
    funcnvmpt
    wph
    @9
    @1
    @0
    cC
    wceq
    #
    wa
    #
    @5
    wi
    #
    vz
    cA
    wral
    #
    vy
    wal
    #
    vx
    cA
    wral
    #
    @3
    wph
    @8
    @14
    vx
    cA
    funcnvmpt.0
    wph
    @4
    cA
    wcel
    wa
    #
    @8
    @12
    vy
    wal
    #
    vz
    cA
    wral
    @14
    @16
    @7
    @17
    vz
    cA
    @16
    @6
    wn
    #
    @5
    wi
    #
    @11
    vy
    wex
    #
    @5
    wi
    @7
    @17
    @16
    @18
    @20
    @5
    @18
    cB
    cC
    wceq
    #
    @16
    @20
    cB
    cC
    nne
    @16
    cB
    cV
    wcel
    @21
    @20
    wb
    funcnvmpt.4
    vy
    cB
    cC
    cV
    eqvincg
    syl
    syl5bb
    imbi1d
    @7
    @6
    @5
    wo
    @19
    @5
    @6
    orcom
    @6
    @5
    df-or
    bitri
    @11
    @5
    vy
    19.23v
    3bitr4g
    ralbidv
    @12
    vz
    vy
    cA
    ralcom4
    syl6bb
    ralbida
    @3
    @13
    vx
    cA
    wral
    #
    vy
    wal
    @15
    @2
    @22
    vy
    @1
    @10
    vx
    vz
    cA
    funcnvmpt.1
    vz
    cA
    nfcv
    @10
    vx
    nfv
    @5
    cB
    cC
    @0
    funcnv5mpt.1
    eqeq2d
    rmo4f
    albii
    @13
    vx
    vy
    cA
    ralcom4
    bitr4i
    syl6bbr
    bitr4d
end
