include "crn.mm"
include "wral.mm"
include "cv.mm"
include "wceq.mm"
include "wrex.mm"
include "wi.mm"
include "wal.mm"
include "wcel.mm"
include "cab.mm"
include "rnmpt2.mm"
include "raleqi.mm"
include "eqeq1.mm"
include "2rexbidv.mm"
include "ralab.mm"
include "ralcom4.mm"
include "r19.23v.mm"
include "albii.mm"
include "bitr2i.mm"
include "3bitri.mm"
include "wb.mm"
include "bitri.mm"
include "nfv.mm"
include "ceqsalg.mm"
include "ralimi.mm"
include "ralbi.mm"
include "syl.mm"
include "syl5bbr.mm"
include "syl5bb.mm"

theorem ralrnmpt2
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F
  let cV: class V
  let vw: setvar w
  let cD: class D
  assume rngop.1: |- F = ( x e. A , y e. B |-> C )
  assume ralrnmpt2.2: |- ( z = C -> ( ph <-> ps ) )

  disjoint y z
  disjoint A y
  disjoint A z
  disjoint B z
  disjoint C z
  disjoint F z
  disjoint ps z
  disjoint x y
  disjoint x z
  disjoint ph x
  disjoint ph y
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint A w
  disjoint B w
  disjoint C w
  disjoint F w
  disjoint D x
  disjoint D y
  disjoint D z
  assert |- ( A. x e. A A. y e. B C e. V -> ( A. z e. ran F ph <-> A. x e. A A. y e. B ps ) )

  proof
    wph
    vz
    cF
    crn
    #
    wral
    #
    vz
    cv
    #
    cC
    wceq
    #
    vy
    cB
    wrex
    #
    wph
    wi
    #
    vz
    wal
    #
    vx
    cA
    wral
    #
    cC
    cV
    wcel
    #
    vy
    cB
    wral
    #
    vx
    cA
    wral
    #
    wps
    vy
    cB
    wral
    #
    vx
    cA
    wral
    #
    @1
    wph
    vz
    vw
    cv
    #
    cC
    wceq
    #
    vy
    cB
    wrex
    vx
    cA
    wrex
    #
    vw
    cab
    #
    wral
    @4
    vx
    cA
    wrex
    #
    wph
    wi
    #
    vz
    wal
    #
    @7
    wph
    vz
    @0
    @16
    vx
    vy
    vw
    cA
    cB
    cC
    cF
    rngop.1
    rnmpt2
    raleqi
    @15
    @17
    wph
    vz
    vw
    @13
    @2
    wceq
    @14
    @3
    vx
    vy
    cA
    cB
    @13
    @2
    cC
    eqeq1
    2rexbidv
    ralab
    @7
    @5
    vx
    cA
    wral
    #
    vz
    wal
    @19
    @5
    vx
    vz
    cA
    ralcom4
    @20
    @18
    vz
    @4
    wph
    vx
    cA
    r19.23v
    albii
    bitr2i
    3bitri
    @10
    @6
    @11
    wb
    #
    vx
    cA
    wral
    @7
    @12
    wb
    @9
    @21
    vx
    cA
    @6
    @3
    wph
    wi
    #
    vz
    wal
    #
    vy
    cB
    wral
    #
    @9
    @11
    @24
    @22
    vy
    cB
    wral
    #
    vz
    wal
    @6
    @22
    vy
    vz
    cB
    ralcom4
    @25
    @5
    vz
    @3
    wph
    vy
    cB
    r19.23v
    albii
    bitri
    @9
    @23
    wps
    wb
    #
    vy
    cB
    wral
    @24
    @11
    wb
    @8
    @26
    vy
    cB
    wph
    wps
    vz
    cC
    cV
    wps
    vz
    nfv
    ralrnmpt2.2
    ceqsalg
    ralimi
    @23
    wps
    vy
    cB
    ralbi
    syl
    syl5bbr
    ralimi
    @6
    @11
    vx
    cA
    ralbi
    syl
    syl5bb
end
