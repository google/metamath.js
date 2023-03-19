include "cv.mm"
include "c0.mm"
include "wne.mm"
include "wral.mm"
include "cin.mm"
include "wceq.mm"
include "wi.mm"
include "wa.mm"
include "wcel.mm"
include "weu.mm"
include "wex.mm"
include "wal.mm"
include "wrex.mm"
include "wn.mm"
include "kmlem1.mm"
include "raleq.mm"
include "raleqbi1dv.mm"
include "exbidv.mm"
include "imbi12d.mm"
include "cbvalv.mm"
include "kmlem10.mm"
include "ineq2.mm"
include "eleq2d.mm"
include "eubidv.mm"
include "imbi2d.mm"
include "ralbidv.mm"
include "cbvexv.mm"
include "csn.mm"
include "cdif.mm"
include "cuni.mm"
include "kmlem3.mm"
include "ralinexa.mm"
include "rexbii.mm"
include "rexnal.mm"
include "3bitri.mm"
include "ralbii.mm"
include "ralnex.mm"
include "bitri.mm"
include "kmlem12.mm"
include "vex.mm"
include "inex1.mm"
include "spcev.mm"
include "syl6.mm"
include "exlimdv.mm"
include "com12.mm"
include "syl5bir.mm"
include "sylbi.mm"
include "syl.mm"
include "alrimiv.mm"
include "kmlem7.mm"
include "imim1i.mm"
include "wb.mm"
include "biimt.mm"
include "ralimi.mm"
include "ralbi.mm"
include "adantr.mm"
include "pm5.74i.mm"
include "sylibr.mm"
include "alimi.mm"
include "impbii.mm"

theorem kmlem13
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let vv: setvar v
  let vu: setvar u
  let vt: setvar t
  let cA: class A
  let vh: setvar h
  let vg: setvar g
  let wph: wff ph
  assume kmlem9.1: |- A = { u | E. t e. x u = ( t \ U. ( x \ { t } ) ) }

  disjoint x y
  disjoint x z
  disjoint w x
  disjoint v x
  disjoint u x
  disjoint t x
  disjoint y z
  disjoint w y
  disjoint v y
  disjoint u y
  disjoint t y
  disjoint w z
  disjoint v z
  disjoint u z
  disjoint t z
  disjoint v w
  disjoint u w
  disjoint t w
  disjoint u v
  disjoint t v
  disjoint t u
  disjoint A y
  disjoint A z
  disjoint A w
  disjoint A v
  disjoint h x
  disjoint g x
  disjoint h y
  disjoint g y
  disjoint h z
  disjoint g z
  disjoint h w
  disjoint g w
  disjoint h v
  disjoint g v
  disjoint h u
  disjoint g u
  disjoint h t
  disjoint g t
  disjoint g h
  disjoint A h
  disjoint A g
  disjoint h ph
  assert |- ( A. x ( ( A. z e. x z =/= (/) /\ A. z e. x A. w e. x ( z =/= w -> ( z i^i w ) = (/) ) ) -> E. y A. z e. x E! v v e. ( z i^i y ) ) <-> A. x ( -. E. z e. x A. v e. z E. w e. x ( z =/= w /\ v e. ( z i^i w ) ) -> E. y A. z e. x ( z =/= (/) -> E! v v e. ( z i^i y ) ) ) )

  proof
    vz
    cv
    #
    c0
    wne
    #
    vz
    vx
    cv
    #
    wral
    #
    @0
    vw
    cv
    #
    wne
    #
    @0
    @4
    cin
    #
    c0
    wceq
    wi
    #
    vw
    @2
    wral
    #
    vz
    @2
    wral
    #
    wa
    #
    vv
    cv
    #
    @0
    vy
    cv
    #
    cin
    #
    wcel
    #
    vv
    weu
    #
    vz
    @2
    wral
    #
    vy
    wex
    #
    wi
    #
    vx
    wal
    #
    @5
    @11
    @6
    wcel
    #
    wa
    vw
    @2
    wrex
    #
    vv
    @0
    wral
    #
    vz
    @2
    wrex
    wn
    #
    @1
    @15
    wi
    #
    vz
    @2
    wral
    #
    vy
    wex
    #
    wi
    #
    vx
    wal
    #
    @19
    @9
    @26
    wi
    #
    vx
    wal
    #
    @28
    @7
    @15
    vx
    vy
    vz
    vw
    kmlem1
    @30
    @7
    vw
    vh
    cv
    #
    wral
    #
    vz
    @31
    wral
    #
    @24
    vz
    @31
    wral
    #
    vy
    wex
    #
    wi
    #
    vh
    wal
    #
    @28
    @29
    @36
    vx
    vh
    @2
    @31
    wceq
    #
    @9
    @33
    @26
    @35
    @8
    @32
    vz
    @2
    @31
    @7
    vw
    @2
    @31
    raleq
    raleqbi1dv
    @38
    @25
    @34
    vy
    @24
    vz
    @2
    @31
    raleq
    exbidv
    imbi12d
    cbvalv
    @37
    @27
    vx
    @37
    @24
    vz
    cA
    wral
    #
    vy
    wex
    #
    @27
    @24
    vx
    vy
    vz
    vw
    vu
    vt
    cA
    vh
    kmlem9.1
    kmlem10
    @40
    @1
    @11
    @0
    vg
    cv
    #
    cin
    #
    wcel
    #
    vv
    weu
    #
    wi
    #
    vz
    cA
    wral
    #
    vg
    wex
    #
    @27
    @39
    @46
    vy
    vg
    @12
    @41
    wceq
    #
    @24
    @45
    vz
    cA
    @48
    @15
    @44
    @1
    @48
    @14
    @43
    vv
    @48
    @13
    @42
    @11
    @12
    @41
    @0
    ineq2
    eleq2d
    eubidv
    imbi2d
    ralbidv
    cbvexv
    @23
    @0
    @2
    @0
    csn
    cdif
    cuni
    cdif
    c0
    wne
    #
    vz
    @2
    wral
    #
    @47
    @26
    @50
    @22
    wn
    #
    vz
    @2
    wral
    @23
    @49
    @51
    vz
    @2
    @49
    @5
    @20
    wn
    wi
    vw
    @2
    wral
    #
    vv
    @0
    wrex
    @21
    wn
    #
    vv
    @0
    wrex
    @51
    vx
    vz
    vw
    vv
    kmlem3
    @52
    @53
    vv
    @0
    @5
    @20
    vw
    @2
    ralinexa
    rexbii
    @21
    vv
    @0
    rexnal
    3bitri
    ralbii
    @22
    vz
    @2
    ralnex
    bitri
    @50
    @47
    @26
    @50
    @46
    @26
    vg
    @50
    @46
    @1
    @11
    @0
    @41
    cA
    cuni
    #
    cin
    #
    cin
    #
    wcel
    #
    vv
    weu
    #
    wi
    #
    vz
    @2
    wral
    #
    @26
    vx
    vg
    vz
    vv
    vu
    vt
    cA
    kmlem9.1
    kmlem12
    @25
    @60
    vy
    @55
    @41
    @54
    vg
    vex
    inex1
    @12
    @55
    wceq
    #
    @24
    @59
    vz
    @2
    @61
    @15
    @58
    @1
    @61
    @14
    @57
    vv
    @61
    @13
    @56
    @11
    @12
    @55
    @0
    ineq2
    eleq2d
    eubidv
    imbi2d
    ralbidv
    spcev
    syl6
    exlimdv
    com12
    syl5bir
    sylbi
    syl
    alrimiv
    sylbi
    syl
    @27
    @18
    vx
    @27
    @10
    @26
    wi
    @18
    @10
    @23
    @26
    vx
    vz
    vw
    vv
    kmlem7
    imim1i
    @10
    @17
    @26
    @3
    @17
    @26
    wb
    @9
    @3
    @16
    @25
    vy
    @3
    @15
    @24
    wb
    #
    vz
    @2
    wral
    @16
    @25
    wb
    @1
    @62
    vz
    @2
    @1
    @15
    biimt
    ralimi
    @15
    @24
    vz
    @2
    ralbi
    syl
    exbidv
    adantr
    pm5.74i
    sylibr
    alimi
    impbii
end
