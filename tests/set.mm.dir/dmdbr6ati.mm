include "cdmd.mm"
include "wbr.mm"
include "chj.mm"
include "co.mm"
include "cv.mm"
include "cin.mm"
include "wceq.mm"
include "cat.mm"
include "wral.mm"
include "cch.mm"
include "wcel.mm"
include "wb.mm"
include "dmdbr3.mm"
include "mp2an.mm"
include "wa.mm"
include "incom.mm"
include "inass.mm"
include "3eqtri.mm"
include "chabs2.mm"
include "mpan2.mm"
include "ineq2d.mm"
include "syl5reqr.mm"
include "adantr.mm"
include "ineq1.mm"
include "adantl.mm"
include "eqtr4d.mm"
include "ralimiaa.mm"
include "sylbi.mm"
include "atelch.mm"
include "imim1i.mm"
include "ralimi2.mm"
include "syl.mm"
include "wss.mm"
include "wi.mm"
include "inss1.mm"
include "sseq1.mm"
include "mpbiri.mm"
include "df-ss.mm"
include "biimpi.mm"
include "syl5eq.mm"
include "sseq1d.mm"
include "syl5ibcom.mm"
include "ralimi.mm"
include "dmdbr5ati.mm"
include "sylibr.mm"
include "impbii.mm"

theorem dmdbr6ati
  let vx: setvar x
  let cA: class A
  let cB: class B
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let cC: class C
  assume sumdmdi.1: |- A e. CH
  assume sumdmdi.2: |- B e. CH

  disjoint A x
  disjoint B x
  disjoint x y
  disjoint x z
  disjoint w x
  disjoint y z
  disjoint w y
  disjoint A y
  disjoint w z
  disjoint A z
  disjoint A w
  disjoint B y
  disjoint B z
  disjoint B w
  disjoint C y
  disjoint C z
  disjoint C w
  assert |- ( A MH* B <-> A. x e. HAtoms ( ( A vH B ) i^i x ) = ( ( ( ( x vH B ) i^i A ) vH B ) i^i x ) )

  proof
    cA
    cB
    cdmd
    wbr
    #
    cA
    cB
    chj
    co
    #
    vx
    cv
    #
    cin
    #
    @2
    cB
    chj
    co
    #
    cA
    cin
    cB
    chj
    co
    #
    @2
    cin
    #
    wceq
    #
    vx
    cat
    wral
    #
    @0
    @7
    vx
    cch
    wral
    #
    @8
    @0
    @5
    @4
    @1
    cin
    #
    wceq
    #
    vx
    cch
    wral
    #
    @9
    cA
    cch
    wcel
    cB
    cch
    wcel
    #
    @0
    @12
    wb
    sumdmdi.1
    sumdmdi.2
    vx
    cA
    cB
    dmdbr3
    mp2an
    @11
    @7
    vx
    cch
    @2
    cch
    wcel
    #
    @11
    wa
    @3
    @10
    @2
    cin
    #
    @6
    @14
    @3
    @15
    wceq
    @11
    @14
    @15
    @1
    @2
    @4
    cin
    #
    cin
    #
    @3
    @17
    @16
    @1
    cin
    @2
    @10
    cin
    @15
    @1
    @16
    incom
    @2
    @4
    @1
    inass
    @2
    @10
    incom
    3eqtri
    @14
    @16
    @2
    @1
    @14
    @13
    @16
    @2
    wceq
    sumdmdi.2
    @2
    cB
    chabs2
    mpan2
    ineq2d
    syl5reqr
    adantr
    @11
    @6
    @15
    wceq
    @14
    @5
    @10
    @2
    ineq1
    adantl
    eqtr4d
    ralimiaa
    sylbi
    @7
    @7
    vx
    cch
    cat
    @2
    cat
    wcel
    @14
    @7
    @2
    atelch
    imim1i
    ralimi2
    syl
    @8
    @2
    @1
    wss
    #
    @2
    @5
    wss
    #
    wi
    #
    vx
    cat
    wral
    @0
    @7
    @20
    vx
    cat
    @7
    @3
    @5
    wss
    #
    @18
    @19
    @7
    @21
    @6
    @5
    wss
    @5
    @2
    inss1
    @3
    @6
    @5
    sseq1
    mpbiri
    @18
    @3
    @2
    @5
    @18
    @3
    @2
    @1
    cin
    #
    @2
    @1
    @2
    incom
    @18
    @22
    @2
    wceq
    @2
    @1
    df-ss
    biimpi
    syl5eq
    sseq1d
    syl5ibcom
    ralimi
    vx
    cA
    cB
    sumdmdi.1
    sumdmdi.2
    dmdbr5ati
    sylibr
    impbii
end
