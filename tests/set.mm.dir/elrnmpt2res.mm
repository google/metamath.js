include "wcel.mm"
include "cres.mm"
include "crn.mm"
include "cv.mm"
include "wa.mm"
include "wceq.mm"
include "wbr.mm"
include "wex.mm"
include "wrex.mm"
include "eqeq1.mm"
include "anbi1d.mm"
include "anbi2d.mm"
include "2exbidv.mm"
include "coprab.mm"
include "cab.mm"
include "cop.mm"
include "copab.mm"
include "an12.mm"
include "ancom.mm"
include "eleq1.mm"
include "df-br.mm"
include "syl6bbr.mm"
include "syl5bbr.mm"
include "syl5bb.mm"
include "pm5.32i.mm"
include "bitri.mm"
include "2exbii.mm"
include "19.42vv.mm"
include "bitr3i.mm"
include "opabbii.mm"
include "dfoprab2.mm"
include "cmpt2.mm"
include "df-mpt2.mm"
include "3eqtri.mm"
include "reseq1i.mm"
include "resopab.mm"
include "eqtri.mm"
include "3eqtr4ri.mm"
include "rneqi.mm"
include "rnoprab.mm"
include "elab2g.mm"
include "r2ex.mm"

theorem elrnmpt2res
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cR: class R
  let cF: class F
  let cV: class V
  let vz: setvar z
  let vp: setvar p
  let vw: setvar w
  let wps: wff ps
  let wph: wff ph
  assume rngop.1: |- F = ( x e. A , y e. B |-> C )

  disjoint x y
  disjoint A y
  disjoint D x
  disjoint D y
  disjoint R x
  disjoint R y
  disjoint A y
  disjoint x y
  disjoint D x
  disjoint D y
  disjoint x z
  disjoint y z
  disjoint A p
  disjoint A z
  disjoint p y
  disjoint p z
  disjoint B p
  disjoint B z
  disjoint C p
  disjoint C z
  disjoint F z
  disjoint D z
  disjoint R p
  disjoint R z
  disjoint p x
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint A w
  disjoint y z
  disjoint A z
  disjoint B w
  disjoint B z
  disjoint C w
  disjoint C z
  disjoint F w
  disjoint F z
  disjoint ps z
  disjoint x z
  disjoint D z
  disjoint ph x
  disjoint ph y
  assert |- ( D e. V -> ( D e. ran ( F |` R ) <-> E. x e. A E. y e. B ( D = C /\ x R y ) ) )

  proof
    cD
    cV
    wcel
    cD
    cF
    cR
    cres
    #
    crn
    #
    wcel
    vx
    cv
    #
    cA
    wcel
    vy
    cv
    #
    cB
    wcel
    wa
    #
    cD
    cC
    wceq
    #
    @2
    @3
    cR
    wbr
    #
    wa
    #
    wa
    #
    vy
    wex
    vx
    wex
    #
    @7
    vy
    cB
    wrex
    vx
    cA
    wrex
    @4
    vz
    cv
    #
    cC
    wceq
    #
    @6
    wa
    #
    wa
    #
    vy
    wex
    vx
    wex
    #
    @9
    vz
    cD
    @1
    cV
    @10
    cD
    wceq
    #
    @13
    @8
    vx
    vy
    @15
    @12
    @7
    @4
    @15
    @11
    @5
    @6
    @10
    cD
    cC
    eqeq1
    anbi1d
    anbi2d
    2exbidv
    @1
    @13
    vx
    vy
    vz
    coprab
    #
    crn
    @14
    vz
    cab
    @0
    @16
    vp
    cv
    #
    @2
    @3
    cop
    #
    wceq
    #
    @13
    wa
    #
    vy
    wex
    vx
    wex
    #
    vp
    vz
    copab
    @17
    cR
    wcel
    #
    @19
    @4
    @11
    wa
    #
    wa
    #
    vy
    wex
    vx
    wex
    #
    wa
    #
    vp
    vz
    copab
    #
    @16
    @0
    @21
    @26
    vp
    vz
    @21
    @22
    @24
    wa
    #
    vy
    wex
    vx
    wex
    @26
    @28
    @20
    vx
    vy
    @28
    @19
    @22
    @23
    wa
    #
    wa
    @20
    @22
    @19
    @23
    an12
    @19
    @29
    @13
    @29
    @4
    @22
    @11
    wa
    #
    wa
    @19
    @13
    @22
    @4
    @11
    an12
    @19
    @30
    @12
    @4
    @30
    @11
    @22
    wa
    @19
    @12
    @11
    @22
    ancom
    @19
    @22
    @6
    @11
    @19
    @22
    @18
    cR
    wcel
    @6
    @17
    @18
    cR
    eleq1
    @2
    @3
    cR
    df-br
    syl6bbr
    anbi2d
    syl5bbr
    anbi2d
    syl5bb
    pm5.32i
    bitri
    2exbii
    @22
    @24
    vx
    vy
    19.42vv
    bitr3i
    opabbii
    @13
    vx
    vy
    vz
    vp
    dfoprab2
    @0
    @25
    vp
    vz
    copab
    #
    cR
    cres
    @27
    cF
    @31
    cR
    cF
    vx
    vy
    cA
    cB
    cC
    cmpt2
    @23
    vx
    vy
    vz
    coprab
    @31
    rngop.1
    vx
    vy
    vz
    cA
    cB
    cC
    df-mpt2
    @23
    vx
    vy
    vz
    vp
    dfoprab2
    3eqtri
    reseq1i
    @25
    vp
    vz
    cR
    resopab
    eqtri
    3eqtr4ri
    rneqi
    @13
    vx
    vy
    vz
    rnoprab
    eqtri
    elab2g
    @7
    vx
    vy
    cA
    cB
    r2ex
    syl6bbr
end
