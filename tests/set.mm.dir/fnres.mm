include "cres.mm"
include "wfun.mm"
include "cdm.mm"
include "wceq.mm"
include "wa.mm"
include "cv.mm"
include "wbr.mm"
include "wex.mm"
include "wmo.mm"
include "wral.mm"
include "wfn.mm"
include "weu.mm"
include "ancom.mm"
include "wal.mm"
include "wcel.mm"
include "wi.mm"
include "vex.mm"
include "brres.mm"
include "bitri.mm"
include "mobii.mm"
include "moanimv.mm"
include "albii.mm"
include "wrel.mm"
include "relres.mm"
include "dffun6.mm"
include "mpbiran.mm"
include "df-ral.mm"
include "3bitr4i.mm"
include "wss.mm"
include "cin.mm"
include "dmres.mm"
include "inss1.mm"
include "eqsstri.mm"
include "eqss.mm"
include "dfss3.mm"
include "elin2.mm"
include "baib.mm"
include "eldm.mm"
include "syl6bb.mm"
include "ralbiia.mm"
include "anbi12i.mm"
include "r19.26.mm"
include "df-fn.mm"
include "eu5.mm"
include "ralbii.mm"

theorem fnres
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cF: class F

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint F x
  disjoint F y
  assert |- ( ( F |` A ) Fn A <-> A. x e. A E! y x F y )

  proof
    cF
    cA
    cres
    #
    wfun
    #
    @0
    cdm
    #
    cA
    wceq
    #
    wa
    #
    vx
    cv
    #
    vy
    cv
    #
    cF
    wbr
    #
    vy
    wex
    #
    @7
    vy
    wmo
    #
    wa
    #
    vx
    cA
    wral
    #
    @0
    cA
    wfn
    @7
    vy
    weu
    #
    vx
    cA
    wral
    @9
    vx
    cA
    wral
    #
    @8
    vx
    cA
    wral
    #
    wa
    @14
    @13
    wa
    @4
    @11
    @13
    @14
    ancom
    @1
    @13
    @3
    @14
    @5
    @6
    @0
    wbr
    #
    vy
    wmo
    #
    vx
    wal
    #
    @5
    cA
    wcel
    #
    @9
    wi
    #
    vx
    wal
    @1
    @13
    @16
    @19
    vx
    @16
    @18
    @7
    wa
    #
    vy
    wmo
    @19
    @15
    @20
    vy
    @15
    @7
    @18
    wa
    @20
    @5
    @6
    cF
    cA
    vy
    vex
    brres
    @7
    @18
    ancom
    bitri
    mobii
    @18
    @7
    vy
    moanimv
    bitri
    albii
    @1
    @0
    wrel
    @17
    cF
    cA
    relres
    vx
    vy
    @0
    dffun6
    mpbiran
    @9
    vx
    cA
    df-ral
    3bitr4i
    @3
    cA
    @2
    wss
    #
    @14
    @3
    @2
    cA
    wss
    @21
    @2
    cA
    cF
    cdm
    #
    cin
    cA
    cF
    cA
    dmres
    #
    cA
    @22
    inss1
    eqsstri
    @2
    cA
    eqss
    mpbiran
    @21
    @5
    @2
    wcel
    #
    vx
    cA
    wral
    @14
    vx
    cA
    @2
    dfss3
    @24
    @8
    vx
    cA
    @18
    @24
    @5
    @22
    wcel
    #
    @8
    @24
    @18
    @25
    @5
    cA
    @22
    @2
    @23
    elin2
    baib
    vy
    @5
    cF
    vx
    vex
    eldm
    syl6bb
    ralbiia
    bitri
    bitri
    anbi12i
    @8
    @9
    vx
    cA
    r19.26
    3bitr4i
    @0
    cA
    df-fn
    @12
    @10
    vx
    cA
    @7
    vy
    eu5
    ralbii
    3bitr4i
end
