include "cv.mm"
include "wceq.mm"
include "wa.mm"
include "wrex.mm"
include "wreu.mm"
include "wcel.mm"
include "weu.mm"
include "csb.mm"
include "crab.mm"
include "wi.mm"
include "wral.mm"
include "df-reu.mm"
include "anass.mm"
include "rabid.mm"
include "anbi1i.mm"
include "eleq1.mm"
include "anbi1d.mm"
include "pm5.32ri.mm"
include "bitr3i.mm"
include "anbi2i.mm"
include "3bitr4ri.mm"
include "rexbii2.mm"
include "r19.42v.mm"
include "nfrab1.mm"
include "nfcv.mm"
include "nfv.mm"
include "nfcsb1v.mm"
include "nfeq2.mm"
include "csbeq1a.mm"
include "eqeq2d.mm"
include "cbvrexf.mm"
include "3bitr3i.mm"
include "eubii.mm"
include "cvv.mm"
include "wb.mm"
include "elex.mm"
include "ad2antrl.mm"
include "sylbi.mm"
include "rgen.mm"
include "nfel1.mm"
include "eleq1d.mm"
include "cbvralf.mm"
include "mpbi.mm"
include "reusv2lem3.mm"
include "ax-mp.mm"
include "wal.mm"
include "df-ral.mm"
include "nfcri.mm"
include "nfim.mm"
include "imbi12d.mm"
include "cbval.mm"
include "imbi1i.mm"
include "impexp.mm"
include "bitri.mm"
include "albii.mm"
include "bitr4i.mm"
include "3bitr2i.mm"
include "3bitri.mm"

theorem reusv2lem4
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let vz: setvar z

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B x
  disjoint C x
  disjoint ph x
  disjoint x z
  disjoint y z
  disjoint A z
  disjoint B z
  disjoint C z
  disjoint ph z
  assert |- ( E! x e. A E. y e. B ( ph /\ x = C ) <-> E! x A. y e. B ( ( C e. A /\ ph ) -> x = C ) )

  proof
    wph
    vx
    cv
    #
    cC
    wceq
    #
    wa
    #
    vy
    cB
    wrex
    #
    vx
    cA
    wreu
    @0
    cA
    wcel
    #
    @3
    wa
    #
    vx
    weu
    @0
    vy
    vz
    cv
    #
    cC
    csb
    #
    wceq
    #
    vz
    cC
    cA
    wcel
    #
    wph
    wa
    #
    vy
    cB
    crab
    #
    wrex
    #
    vx
    weu
    #
    @10
    @1
    wi
    #
    vy
    cB
    wral
    #
    vx
    weu
    #
    @3
    vx
    cA
    df-reu
    @5
    @12
    vx
    @4
    @2
    wa
    #
    vy
    cB
    wrex
    @1
    vy
    @11
    wrex
    @5
    @12
    @17
    @1
    vy
    cB
    @11
    vy
    cv
    #
    cB
    wcel
    #
    @10
    wa
    #
    @1
    wa
    @19
    @10
    @1
    wa
    #
    wa
    @18
    @11
    wcel
    #
    @1
    wa
    @19
    @17
    wa
    @19
    @10
    @1
    anass
    @22
    @20
    @1
    @10
    vy
    cB
    rabid
    #
    anbi1i
    @17
    @21
    @19
    @17
    @4
    wph
    wa
    #
    @1
    wa
    @21
    @4
    wph
    @1
    anass
    @1
    @24
    @10
    @1
    @4
    @9
    wph
    @0
    cC
    cA
    eleq1
    anbi1d
    pm5.32ri
    bitr3i
    anbi2i
    3bitr4ri
    rexbii2
    @4
    @2
    vy
    cB
    r19.42v
    @1
    @8
    vy
    vz
    @11
    @10
    vy
    cB
    nfrab1
    #
    vz
    @11
    nfcv
    #
    @1
    vz
    nfv
    vy
    @0
    @7
    vy
    @6
    cC
    nfcsb1v
    #
    nfeq2
    #
    @18
    @6
    wceq
    #
    cC
    @7
    @0
    vy
    @6
    cC
    csbeq1a
    #
    eqeq2d
    #
    cbvrexf
    3bitr3i
    eubii
    @13
    @8
    vz
    @11
    wral
    #
    vx
    weu
    #
    @16
    @7
    cvv
    wcel
    #
    vz
    @11
    wral
    #
    @13
    @33
    wb
    cC
    cvv
    wcel
    #
    vy
    @11
    wral
    @35
    @36
    vy
    @11
    @22
    @20
    @36
    @23
    @9
    @36
    @19
    wph
    cC
    cA
    elex
    ad2antrl
    sylbi
    rgen
    @36
    @34
    vy
    vz
    @11
    @25
    @26
    @36
    vz
    nfv
    vy
    @7
    cvv
    @27
    nfel1
    @29
    cC
    @7
    cvv
    @30
    eleq1d
    cbvralf
    mpbi
    vx
    vz
    @11
    @7
    reusv2lem3
    ax-mp
    @32
    @15
    vx
    @32
    @6
    @11
    wcel
    #
    @8
    wi
    #
    vz
    wal
    @22
    @1
    wi
    #
    vy
    wal
    #
    @15
    @8
    vz
    @11
    df-ral
    @39
    @38
    vy
    vz
    @39
    vz
    nfv
    @37
    @8
    vy
    vy
    vz
    @11
    @25
    nfcri
    @28
    nfim
    @29
    @22
    @37
    @1
    @8
    @18
    @6
    @11
    eleq1
    @31
    imbi12d
    cbval
    @40
    @19
    @14
    wi
    #
    vy
    wal
    @15
    @39
    @41
    vy
    @39
    @20
    @1
    wi
    @41
    @22
    @20
    @1
    @23
    imbi1i
    @19
    @10
    @1
    impexp
    bitri
    albii
    @14
    vy
    cB
    df-ral
    bitr4i
    3bitr2i
    eubii
    bitri
    3bitri
end
