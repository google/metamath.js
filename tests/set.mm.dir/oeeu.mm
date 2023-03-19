include "con0.mm"
include "c2o.mm"
include "cdif.mm"
include "wcel.mm"
include "c1o.mm"
include "wa.mm"
include "cv.mm"
include "cotp.mm"
include "wceq.mm"
include "coe.mm"
include "co.mm"
include "w3a.mm"
include "comu.mm"
include "coa.mm"
include "wex.mm"
include "weu.mm"
include "wrex.mm"
include "crab.mm"
include "cint.mm"
include "cuni.mm"
include "cop.mm"
include "cio.mm"
include "c1st.mm"
include "cfv.mm"
include "c2nd.mm"
include "cvv.mm"
include "wss.mm"
include "csuc.mm"
include "eqid.mm"
include "oeeulem.mm"
include "simp1d.mm"
include "elex.mm"
include "syl.mm"
include "fvexd.mm"
include "oeeui.mm"
include "euotd.mm"
include "df-3an.mm"
include "ancom.mm"
include "bitri.mm"
include "anbi1i.mm"
include "anbi2i.mm"
include "an12.mm"
include "anass.mm"
include "3bitri.mm"
include "exbii.mm"
include "df-rex.mm"
include "r19.42v.mm"
include "3bitr2i.mm"
include "2exbii.mm"
include "r2ex.mm"
include "bitr4i.mm"
include "eubii.mm"
include "sylib.mm"

theorem oeeu
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let cA: class A
  let cB: class B
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d

  disjoint w x
  disjoint w y
  disjoint w z
  disjoint A w
  disjoint x y
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint B w
  disjoint B x
  disjoint B y
  disjoint B z
  disjoint a b
  disjoint a c
  disjoint a d
  disjoint a w
  disjoint a x
  disjoint a y
  disjoint a z
  disjoint A a
  disjoint b c
  disjoint b d
  disjoint b w
  disjoint b x
  disjoint b y
  disjoint b z
  disjoint A b
  disjoint c d
  disjoint c w
  disjoint c x
  disjoint c y
  disjoint c z
  disjoint A c
  disjoint d w
  disjoint d x
  disjoint d y
  disjoint d z
  disjoint A d
  disjoint B a
  disjoint B b
  disjoint B c
  disjoint B d
  assert |- ( ( A e. ( On \ 2o ) /\ B e. ( On \ 1o ) ) -> E! w E. x e. On E. y e. ( A \ 1o ) E. z e. ( A ^o x ) ( w = <. x , y , z >. /\ ( ( ( A ^o x ) .o y ) +o z ) = B ) )

  proof
    cA
    con0
    c2o
    cdif
    wcel
    cB
    con0
    c1o
    cdif
    wcel
    wa
    #
    vw
    cv
    vx
    cv
    #
    vy
    cv
    #
    vz
    cv
    #
    cotp
    wceq
    #
    @1
    con0
    wcel
    #
    @2
    cA
    c1o
    cdif
    #
    wcel
    #
    @3
    cA
    @1
    coe
    co
    #
    wcel
    #
    w3a
    #
    @8
    @2
    comu
    co
    @3
    coa
    co
    cB
    wceq
    #
    wa
    #
    wa
    #
    vz
    wex
    #
    vy
    wex
    vx
    wex
    #
    vw
    weu
    @4
    @11
    wa
    #
    vz
    @8
    wrex
    #
    vy
    @6
    wrex
    vx
    con0
    wrex
    #
    vw
    weu
    @0
    @12
    vw
    cB
    cA
    va
    cv
    coe
    co
    wcel
    va
    con0
    crab
    cint
    cuni
    #
    vd
    cv
    vb
    cv
    #
    vc
    cv
    #
    cop
    wceq
    cA
    @19
    coe
    co
    #
    @20
    comu
    co
    @21
    coa
    co
    cB
    wceq
    wa
    vc
    @22
    wrex
    vb
    con0
    wrex
    vd
    cio
    #
    c1st
    cfv
    #
    @23
    c2nd
    cfv
    #
    vx
    vy
    vz
    @0
    @19
    con0
    wcel
    #
    @19
    cvv
    wcel
    @0
    @26
    @22
    cB
    wss
    cB
    cA
    @19
    csuc
    coe
    co
    wcel
    va
    cA
    cB
    @19
    @19
    eqid
    #
    oeeulem
    simp1d
    @19
    con0
    elex
    syl
    @0
    @23
    c1st
    fvexd
    @0
    @23
    c2nd
    fvexd
    va
    vb
    vc
    vd
    cA
    cB
    @1
    @2
    @23
    @3
    @19
    @24
    @25
    @27
    @23
    eqid
    @24
    eqid
    @25
    eqid
    oeeui
    euotd
    @15
    @18
    vw
    @15
    @5
    @7
    wa
    #
    @17
    wa
    #
    vy
    wex
    vx
    wex
    @18
    @14
    @29
    vx
    vy
    @14
    @9
    @28
    @16
    wa
    #
    wa
    #
    vz
    wex
    @30
    vz
    @8
    wrex
    @29
    @13
    @31
    vz
    @13
    @4
    @9
    @28
    wa
    #
    @11
    wa
    #
    wa
    @32
    @16
    wa
    @31
    @12
    @33
    @4
    @10
    @32
    @11
    @10
    @28
    @9
    wa
    @32
    @5
    @7
    @9
    df-3an
    @28
    @9
    ancom
    bitri
    anbi1i
    anbi2i
    @4
    @32
    @11
    an12
    @9
    @28
    @16
    anass
    3bitri
    exbii
    @30
    vz
    @8
    df-rex
    @28
    @16
    vz
    @8
    r19.42v
    3bitr2i
    2exbii
    @17
    vx
    vy
    con0
    @6
    r2ex
    bitr4i
    eubii
    sylib
end
