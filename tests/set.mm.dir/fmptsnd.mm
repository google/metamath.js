include "cv.mm"
include "wceq.mm"
include "wa.mm"
include "copab.mm"
include "csn.mm"
include "wcel.mm"
include "cop.mm"
include "cmpt.mm"
include "velsn.mm"
include "bicomi.mm"
include "anbi1i.mm"
include "opabbii.mm"
include "wsbc.mm"
include "eqidd.mm"
include "sbcan.mm"
include "wb.mm"
include "sbcg.mm"
include "syl.mm"
include "eqsbc3.mm"
include "anbi12d.mm"
include "syl5bb.mm"
include "sbcbidv.mm"
include "eqeq1.mm"
include "adantl.mm"
include "eqeq2d.mm"
include "sbcied.mm"
include "bitrd.mm"
include "mpbir2and.mm"
include "opelopabsb.mm"
include "sylibr.mm"
include "eleq1.mm"
include "syl5ibrcom.mm"
include "syl5bi.mm"
include "wex.mm"
include "elopab.mm"
include "wi.mm"
include "opeq12.mm"
include "adantrr.mm"
include "opeq2d.mm"
include "opex.mm"
include "snid.mm"
include "syl6eqel.mm"
include "sylbid.mm"
include "ex.mm"
include "com23.mm"
include "impd.mm"
include "exlimdvv.mm"
include "impbid.mm"
include "eqrdv.mm"
include "df-mpt.mm"
include "a1i.mm"
include "3eqtr4a.mm"

theorem fmptsnd
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cV: class V
  let cW: class W
  let vp: setvar p
  let vy: setvar y
  assume fmptsnd.1: |- ( ( ph /\ x = A ) -> B = C )
  assume fmptsnd.2: |- ( ph -> A e. V )
  assume fmptsnd.3: |- ( ph -> C e. W )

  disjoint A x
  disjoint C x
  disjoint ph x
  disjoint A p
  disjoint A y
  disjoint p x
  disjoint p y
  disjoint x y
  disjoint B p
  disjoint B y
  disjoint C p
  disjoint C y
  disjoint V p
  disjoint W p
  disjoint p ph
  disjoint ph y
  assert |- ( ph -> { <. A , C >. } = ( x e. { A } |-> B ) )

  proof
    wph
    vx
    cv
    #
    cA
    wceq
    #
    vy
    cv
    #
    cB
    wceq
    #
    wa
    #
    vx
    vy
    copab
    #
    @0
    cA
    csn
    #
    wcel
    #
    @3
    wa
    #
    vx
    vy
    copab
    #
    cA
    cC
    cop
    #
    csn
    #
    vx
    @6
    cB
    cmpt
    #
    @4
    @8
    vx
    vy
    @1
    @7
    @3
    @7
    @1
    vx
    cA
    velsn
    bicomi
    anbi1i
    opabbii
    wph
    vp
    @11
    @5
    wph
    vp
    cv
    #
    @11
    wcel
    #
    @13
    @5
    wcel
    #
    @14
    @13
    @10
    wceq
    #
    wph
    @15
    vp
    @10
    velsn
    wph
    @15
    @16
    @10
    @5
    wcel
    #
    wph
    @4
    vy
    cC
    wsbc
    #
    vx
    cA
    wsbc
    #
    @17
    wph
    @19
    cA
    cA
    wceq
    #
    cC
    cC
    wceq
    #
    wph
    cA
    eqidd
    wph
    cC
    eqidd
    wph
    @19
    @1
    cC
    cB
    wceq
    #
    wa
    #
    vx
    cA
    wsbc
    @20
    @21
    wa
    #
    wph
    @18
    @23
    vx
    cA
    @18
    @1
    vy
    cC
    wsbc
    #
    @3
    vy
    cC
    wsbc
    #
    wa
    wph
    @23
    @1
    @3
    vy
    cC
    sbcan
    wph
    @25
    @1
    @26
    @22
    wph
    cC
    cW
    wcel
    #
    @25
    @1
    wb
    fmptsnd.3
    @1
    vy
    cC
    cW
    sbcg
    syl
    wph
    @27
    @26
    @22
    wb
    fmptsnd.3
    vy
    cC
    cB
    cW
    eqsbc3
    syl
    anbi12d
    syl5bb
    sbcbidv
    wph
    @23
    @24
    vx
    cA
    cV
    fmptsnd.2
    wph
    @1
    wa
    #
    @1
    @20
    @22
    @21
    @1
    @1
    @20
    wb
    wph
    @0
    cA
    cA
    eqeq1
    adantl
    @28
    cB
    cC
    cC
    fmptsnd.1
    eqeq2d
    anbi12d
    sbcied
    bitrd
    mpbir2and
    @4
    vx
    vy
    cA
    cC
    opelopabsb
    sylibr
    @13
    @10
    @5
    eleq1
    syl5ibrcom
    syl5bi
    @15
    @13
    @0
    @2
    cop
    #
    wceq
    #
    @4
    wa
    #
    vy
    wex
    vx
    wex
    wph
    @14
    @4
    vx
    vy
    @13
    elopab
    wph
    @31
    @14
    vx
    vy
    wph
    @30
    @4
    @14
    wph
    @4
    @30
    @14
    wph
    @4
    @30
    @14
    wi
    wph
    @4
    wa
    #
    @30
    @13
    cA
    cB
    cop
    #
    wceq
    #
    @14
    @32
    @29
    @33
    @13
    @4
    @29
    @33
    wceq
    wph
    @0
    @2
    cA
    cB
    opeq12
    adantl
    eqeq2d
    @32
    @14
    @34
    @33
    @11
    wcel
    @32
    @33
    @10
    @11
    @32
    cB
    cC
    cA
    wph
    @1
    cB
    cC
    wceq
    @3
    fmptsnd.1
    adantrr
    opeq2d
    @10
    cA
    cC
    opex
    snid
    syl6eqel
    @13
    @33
    @11
    eleq1
    syl5ibrcom
    sylbid
    ex
    com23
    impd
    exlimdvv
    syl5bi
    impbid
    eqrdv
    @12
    @9
    wceq
    wph
    vx
    vy
    @6
    cB
    df-mpt
    a1i
    3eqtr4a
end
