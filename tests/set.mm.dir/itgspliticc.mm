include "cicc.mm"
include "co.mm"
include "cin.mm"
include "covol.mm"
include "cfv.mm"
include "csn.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "cif.mm"
include "cxr.mm"
include "wcel.mm"
include "wceq.mm"
include "rexrd.mm"
include "cr.mm"
include "w3a.mm"
include "wb.mm"
include "elicc2.mm"
include "syl2anc.mm"
include "mpbid.mm"
include "simp1d.mm"
include "df-icc.mm"
include "cv.mm"
include "xrmaxle.mm"
include "xrlemin.mm"
include "ixxin.mm"
include "syl22anc.mm"
include "simp2d.mm"
include "iftrued.mm"
include "simp3d.mm"
include "oveq12d.mm"
include "iccid.mm"
include "syl.mm"
include "3eqtrd.mm"
include "fveq2d.mm"
include "ovolsn.mm"
include "eqtrd.mm"
include "cun.mm"
include "iccsplit.mm"
include "syl3anc.mm"
include "itgsplit.mm"

theorem itgspliticc
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cV: class V
  let vy: setvar y
  let vz: setvar z
  assume itgspliticc.1: |- ( ph -> A e. RR )
  assume itgspliticc.2: |- ( ph -> C e. RR )
  assume itgspliticc.3: |- ( ph -> B e. ( A [,] C ) )
  assume itgspliticc.4: |- ( ( ph /\ x e. ( A [,] C ) ) -> D e. V )
  assume itgspliticc.5: |- ( ph -> ( x e. ( A [,] B ) |-> D ) e. L^1 )
  assume itgspliticc.6: |- ( ph -> ( x e. ( B [,] C ) |-> D ) e. L^1 )

  disjoint A x
  disjoint B x
  disjoint C x
  disjoint V x
  disjoint ph x
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint B y
  disjoint B z
  disjoint C y
  disjoint C z
  assert |- ( ph -> S. ( A [,] C ) D _d x = ( S. ( A [,] B ) D _d x + S. ( B [,] C ) D _d x ) )

  proof
    wph
    vx
    cA
    cB
    cicc
    co
    #
    cB
    cC
    cicc
    co
    #
    cD
    cA
    cC
    cicc
    co
    #
    cV
    wph
    @0
    @1
    cin
    #
    covol
    cfv
    cB
    csn
    #
    covol
    cfv
    #
    cc0
    wph
    @3
    @4
    covol
    wph
    @3
    cA
    cB
    cle
    wbr
    #
    cB
    cA
    cif
    #
    cB
    cC
    cle
    wbr
    #
    cB
    cC
    cif
    #
    cicc
    co
    #
    cB
    cB
    cicc
    co
    #
    @4
    wph
    cA
    cxr
    wcel
    cB
    cxr
    wcel
    #
    @12
    cC
    cxr
    wcel
    @3
    @10
    wceq
    wph
    cA
    itgspliticc.1
    rexrd
    wph
    cB
    wph
    cB
    cr
    wcel
    #
    @6
    @8
    wph
    cB
    @2
    wcel
    #
    @13
    @6
    @8
    w3a
    #
    itgspliticc.3
    wph
    cA
    cr
    wcel
    #
    cC
    cr
    wcel
    #
    @14
    @15
    wb
    itgspliticc.1
    itgspliticc.2
    cA
    cC
    cB
    elicc2
    syl2anc
    mpbid
    #
    simp1d
    #
    rexrd
    #
    @20
    wph
    cC
    itgspliticc.2
    rexrd
    vx
    vy
    vz
    cA
    cB
    cB
    cC
    cle
    cle
    cicc
    vx
    vy
    vz
    df-icc
    cA
    cB
    vz
    cv
    #
    xrmaxle
    @21
    cB
    cC
    xrlemin
    ixxin
    syl22anc
    wph
    @7
    cB
    @9
    cB
    cicc
    wph
    @6
    cB
    cA
    wph
    @13
    @6
    @8
    @18
    simp2d
    iftrued
    wph
    @8
    cB
    cC
    wph
    @13
    @6
    @8
    @18
    simp3d
    iftrued
    oveq12d
    wph
    @12
    @11
    @4
    wceq
    @20
    cB
    iccid
    syl
    3eqtrd
    fveq2d
    wph
    @13
    @5
    cc0
    wceq
    @19
    cB
    ovolsn
    syl
    eqtrd
    wph
    @16
    @17
    @14
    @2
    @0
    @1
    cun
    wceq
    itgspliticc.1
    itgspliticc.2
    itgspliticc.3
    cA
    cC
    cB
    iccsplit
    syl3anc
    itgspliticc.4
    itgspliticc.5
    itgspliticc.6
    itgsplit
end
