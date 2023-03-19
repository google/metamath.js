include "wceq.mm"
include "cv.mm"
include "wi.mm"
include "wral.mm"
include "wn.mm"
include "wne.mm"
include "wa.mm"
include "wrex.mm"
include "cdom.mm"
include "wbr.mm"
include "csdm.mm"
include "domnsym.mm"
include "nsyl3.mm"
include "cvv.mm"
include "wcel.mm"
include "relsdom.mm"
include "brrelexi.mm"
include "syl.mm"
include "adantr.mm"
include "csb.mm"
include "nfv.mm"
include "nfcsb1v.mm"
include "nfel1.mm"
include "nfim.mm"
include "eleq1.mm"
include "anbi2d.mm"
include "csbeq1a.mm"
include "eleq1d.mm"
include "imbi12d.mm"
include "chvar.mm"
include "ex.mm"
include "wb.mm"
include "csbid.mm"
include "vex.mm"
include "csbie.mm"
include "eqeq12i.mm"
include "imbi1i.mm"
include "2ralbii.mm"
include "nfeq.mm"
include "csbeq1.mm"
include "eqeq1d.mm"
include "equequ1.mm"
include "eqeq2d.mm"
include "equequ2.mm"
include "rspc2.mm"
include "com12.mm"
include "sylbir.mm"
include "id.mm"
include "impbid1.mm"
include "syl6.mm"
include "adantl.mm"
include "dom2d.mm"
include "mpd.mm"
include "mtand.mm"
include "ancom.mm"
include "df-ne.mm"
include "anbi1i.mm"
include "pm4.61.mm"
include "3bitr4i.mm"
include "rexbii.mm"
include "rexnal.mm"
include "bitri.mm"
include "sylibr.mm"

theorem fphpd
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let va: setvar a
  let vb: setvar b
  assume fphpd.a: |- ( ph -> B ~< A )
  assume fphpd.b: |- ( ( ph /\ x e. A ) -> C e. B )
  assume fphpd.c: |- ( x = y -> C = D )

  disjoint A x
  disjoint A y
  disjoint x y
  disjoint B x
  disjoint B y
  disjoint C y
  disjoint D x
  disjoint ph x
  disjoint ph y
  disjoint A a
  disjoint A b
  disjoint a x
  disjoint b x
  disjoint a y
  disjoint b y
  disjoint a b
  disjoint B a
  disjoint B b
  disjoint C a
  disjoint C b
  disjoint D a
  disjoint D b
  disjoint a ph
  disjoint b ph
  assert |- ( ph -> E. x e. A E. y e. A ( x =/= y /\ C = D ) )

  proof
    wph
    cC
    cD
    wceq
    #
    vx
    cv
    #
    vy
    cv
    #
    wceq
    #
    wi
    #
    vy
    cA
    wral
    #
    vx
    cA
    wral
    #
    wn
    #
    @1
    @2
    wne
    #
    @0
    wa
    #
    vy
    cA
    wrex
    #
    vx
    cA
    wrex
    #
    wph
    @6
    cA
    cB
    cdom
    wbr
    #
    @12
    cB
    cA
    csdm
    wbr
    #
    wph
    cA
    cB
    domnsym
    fphpd.a
    nsyl3
    wph
    @6
    wa
    #
    cB
    cvv
    wcel
    #
    @12
    wph
    @15
    @6
    wph
    @13
    @15
    fphpd.a
    cB
    cA
    csdm
    relsdom
    brrelexi
    syl
    adantr
    @14
    va
    vb
    cA
    cB
    vx
    va
    cv
    #
    cC
    csb
    #
    vx
    vb
    cv
    #
    cC
    csb
    #
    cvv
    wph
    @16
    cA
    wcel
    #
    @17
    cB
    wcel
    #
    wi
    @6
    wph
    @20
    @21
    wph
    @1
    cA
    wcel
    #
    wa
    #
    cC
    cB
    wcel
    #
    wi
    wph
    @20
    wa
    #
    @21
    wi
    vx
    va
    @25
    @21
    vx
    @25
    vx
    nfv
    vx
    @17
    cB
    vx
    @16
    cC
    nfcsb1v
    #
    nfel1
    nfim
    @1
    @16
    wceq
    #
    @23
    @25
    @24
    @21
    @27
    @22
    @20
    wph
    @1
    @16
    cA
    eleq1
    anbi2d
    @27
    cC
    @17
    cB
    vx
    @16
    cC
    csbeq1a
    eleq1d
    imbi12d
    fphpd.b
    chvar
    ex
    adantr
    @6
    @20
    @18
    cA
    wcel
    wa
    #
    @17
    @19
    wceq
    #
    @16
    @18
    wceq
    #
    wb
    #
    wi
    wph
    @6
    @28
    @29
    @30
    wi
    #
    @31
    @6
    vx
    @1
    cC
    csb
    #
    vx
    @2
    cC
    csb
    #
    wceq
    #
    @3
    wi
    #
    vy
    cA
    wral
    vx
    cA
    wral
    #
    @28
    @32
    wi
    @36
    @4
    vx
    vy
    cA
    cA
    @35
    @0
    @3
    @33
    cC
    @34
    cD
    vx
    cC
    csbid
    vx
    @2
    cC
    cD
    vy
    vex
    fphpd.c
    csbie
    eqeq12i
    imbi1i
    2ralbii
    @28
    @37
    @32
    @36
    @32
    @17
    @34
    wceq
    #
    @16
    @2
    wceq
    #
    wi
    vx
    vy
    @16
    @18
    cA
    cA
    @38
    @39
    vx
    vx
    @17
    @34
    @26
    vx
    @2
    cC
    nfcsb1v
    nfeq
    @39
    vx
    nfv
    nfim
    @32
    vy
    nfv
    @27
    @35
    @38
    @3
    @39
    @27
    @33
    @17
    @34
    vx
    @1
    @16
    cC
    csbeq1
    eqeq1d
    vx
    va
    vy
    equequ1
    imbi12d
    @2
    @18
    wceq
    #
    @38
    @29
    @39
    @30
    @40
    @34
    @19
    @17
    vx
    @2
    @18
    cC
    csbeq1
    eqeq2d
    vy
    vb
    va
    equequ2
    imbi12d
    rspc2
    com12
    sylbir
    @32
    @29
    @30
    @32
    id
    vx
    @16
    @18
    cC
    csbeq1
    impbid1
    syl6
    adantl
    dom2d
    mpd
    mtand
    @11
    @5
    wn
    #
    vx
    cA
    wrex
    @7
    @10
    @41
    vx
    cA
    @10
    @4
    wn
    #
    vy
    cA
    wrex
    @41
    @9
    @42
    vy
    cA
    @3
    wn
    #
    @0
    wa
    @0
    @43
    wa
    @9
    @42
    @43
    @0
    ancom
    @8
    @43
    @0
    @1
    @2
    df-ne
    anbi1i
    @0
    @3
    pm4.61
    3bitr4i
    rexbii
    @4
    vy
    cA
    rexnal
    bitri
    rexbii
    @5
    vx
    cA
    rexnal
    bitri
    sylibr
end
