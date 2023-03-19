include "cdmd.mm"
include "wbr.mm"
include "chj.mm"
include "co.mm"
include "cv.mm"
include "cin.mm"
include "wss.mm"
include "cat.mm"
include "wral.mm"
include "wceq.mm"
include "dmdbr6ati.mm"
include "inss1.mm"
include "sseq1.mm"
include "mpbiri.mm"
include "ralimi.mm"
include "sylbi.mm"
include "wi.mm"
include "sseqin2.mm"
include "biimpi.mm"
include "sseq1d.mm"
include "biimpcd.mm"
include "dmdbr5ati.mm"
include "sylibr.mm"
include "impbii.mm"

theorem dmdbr7ati
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
  assert |- ( A MH* B <-> A. x e. HAtoms ( ( A vH B ) i^i x ) C_ ( ( ( x vH B ) i^i A ) vH B ) )

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
    cA
    cin
    cB
    chj
    co
    #
    wss
    #
    vx
    cat
    wral
    #
    @0
    @3
    @4
    @2
    cin
    #
    wceq
    #
    vx
    cat
    wral
    @6
    vx
    cA
    cB
    sumdmdi.1
    sumdmdi.2
    dmdbr6ati
    @8
    @5
    vx
    cat
    @8
    @5
    @7
    @4
    wss
    @4
    @2
    inss1
    @3
    @7
    @4
    sseq1
    mpbiri
    ralimi
    sylbi
    @6
    @2
    @1
    wss
    #
    @2
    @4
    wss
    #
    wi
    #
    vx
    cat
    wral
    @0
    @5
    @11
    vx
    cat
    @9
    @5
    @10
    @9
    @3
    @2
    @4
    @9
    @3
    @2
    wceq
    @2
    @1
    sseqin2
    biimpi
    sseq1d
    biimpcd
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
