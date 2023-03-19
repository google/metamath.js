include "wcel.mm"
include "wral.mm"
include "cv.mm"
include "cab.mm"
include "wceq.mm"
include "wrex.mm"
include "wi.mm"
include "wal.mm"
include "ciin.mm"
include "cint.mm"
include "df-ral.mm"
include "wb.mm"
include "eleq2.mm"
include "biimprcd.mm"
include "alrimiv.mm"
include "eqid.mm"
include "eqeq1.mm"
include "imbi12d.mm"
include "spcgv.mm"
include "mpii.mm"
include "impbid2.mm"
include "imim2i.mm"
include "pm5.74d.mm"
include "alimi.mm"
include "albi.mm"
include "syl.mm"
include "sylbi.mm"
include "albii.mm"
include "alcom.mm"
include "bitr4i.mm"
include "r19.23v.mm"
include "vex.mm"
include "rexbidv.mm"
include "elab.mm"
include "imbi1i.mm"
include "19.21v.mm"
include "3bitr3ri.mm"
include "syl6bb.mm"
include "syl5bb.mm"
include "abbidv.mm"
include "df-iin.mm"
include "df-int.mm"
include "3eqtr4g.mm"

theorem dfiin2g
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let vz: setvar z
  let vw: setvar w

  disjoint A y
  disjoint B y
  disjoint x y
  disjoint y z
  disjoint w y
  disjoint w z
  disjoint A z
  disjoint A w
  disjoint B z
  disjoint B w
  disjoint C w
  disjoint C z
  disjoint w x
  disjoint x z
  assert |- ( A. x e. A B e. C -> |^|_ x e. A B = |^| { y | E. x e. A y = B } )

  proof
    cB
    cC
    wcel
    #
    vx
    cA
    wral
    #
    vw
    cv
    #
    cB
    wcel
    #
    vx
    cA
    wral
    #
    vw
    cab
    vz
    cv
    #
    vy
    cv
    #
    cB
    wceq
    #
    vx
    cA
    wrex
    #
    vy
    cab
    #
    wcel
    #
    @2
    @5
    wcel
    #
    wi
    #
    vz
    wal
    #
    vw
    cab
    vx
    cA
    cB
    ciin
    @9
    cint
    @1
    @4
    @13
    vw
    @4
    vx
    cv
    cA
    wcel
    #
    @3
    wi
    #
    vx
    wal
    #
    @1
    @13
    @3
    vx
    cA
    df-ral
    @1
    @16
    @14
    @5
    cB
    wceq
    #
    @11
    wi
    #
    vz
    wal
    #
    wi
    #
    vx
    wal
    #
    @13
    @1
    @14
    @0
    wi
    #
    vx
    wal
    #
    @16
    @21
    wb
    #
    @0
    vx
    cA
    df-ral
    @23
    @15
    @20
    wb
    #
    vx
    wal
    @24
    @22
    @25
    vx
    @22
    @14
    @3
    @19
    @0
    @3
    @19
    wb
    @14
    @0
    @3
    @19
    @3
    @18
    vz
    @17
    @11
    @3
    @5
    cB
    @2
    eleq2
    #
    biimprcd
    alrimiv
    @0
    @19
    cB
    cB
    wceq
    #
    @3
    cB
    eqid
    @18
    @27
    @3
    wi
    vz
    cB
    cC
    @17
    @17
    @27
    @11
    @3
    @5
    cB
    cB
    eqeq1
    @26
    imbi12d
    spcgv
    mpii
    impbid2
    imim2i
    pm5.74d
    alimi
    @15
    @20
    vx
    albi
    syl
    sylbi
    @18
    vx
    cA
    wral
    #
    vz
    wal
    #
    @14
    @18
    wi
    #
    vz
    wal
    #
    vx
    wal
    #
    @13
    @21
    @29
    @30
    vx
    wal
    #
    vz
    wal
    @32
    @28
    @33
    vz
    @18
    vx
    cA
    df-ral
    albii
    @30
    vx
    vz
    alcom
    bitr4i
    @28
    @12
    vz
    @28
    @17
    vx
    cA
    wrex
    #
    @11
    wi
    @12
    @17
    @11
    vx
    cA
    r19.23v
    @10
    @34
    @11
    @8
    @34
    vy
    @5
    vz
    vex
    @6
    @5
    wceq
    @7
    @17
    vx
    cA
    @6
    @5
    cB
    eqeq1
    rexbidv
    elab
    imbi1i
    bitr4i
    albii
    @31
    @20
    vx
    @14
    @18
    vz
    19.21v
    albii
    3bitr3ri
    syl6bb
    syl5bb
    abbidv
    vx
    vw
    cA
    cB
    df-iin
    vw
    vz
    @9
    df-int
    3eqtr4g
end
