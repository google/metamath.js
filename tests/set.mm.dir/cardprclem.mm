include "cvv.mm"
include "wcel.mm"
include "cuni.mm"
include "char.mm"
include "cfv.mm"
include "wa.mm"
include "con0.mm"
include "cdom.mm"
include "wbr.mm"
include "wss.mm"
include "cv.mm"
include "csdm.mm"
include "wral.mm"
include "ccrd.mm"
include "wceq.mm"
include "cab.mm"
include "eleq2i.mm"
include "abid.mm"
include "iscard.mm"
include "3bitri.mm"
include "simplbi.mm"
include "ssriv.mm"
include "ssonuni.mm"
include "mpi.mm"
include "domrefg.mm"
include "syl.mm"
include "elharval.mm"
include "sylanbrc.mm"
include "wex.mm"
include "sseli.mm"
include "ancli.mm"
include "sylibr.mm"
include "harcard.mm"
include "fvex.mm"
include "fveq2.mm"
include "id.mm"
include "eqeq12d.mm"
include "elab2.mm"
include "mpbir.mm"
include "eleq2.mm"
include "eleq1.mm"
include "anbi12d.mm"
include "spcev.mm"
include "sylancl.mm"
include "eluni.mm"
include "sselii.mm"
include "jctir.mm"
include "word.mm"
include "wn.mm"
include "eloni.mm"
include "ordn2lp.mm"
include "3syl.mm"
include "pm2.65i.mm"

theorem cardprclem
  let vx: setvar x
  let cA: class A
  let vw: setvar w
  let vy: setvar y
  let vz: setvar z
  assume cardprclem.1: |- A = { x | ( card ` x ) = x }

  disjoint A x
  disjoint A w
  disjoint A y
  disjoint A z
  disjoint w y
  disjoint w z
  disjoint y z
  disjoint x y
  disjoint x z
  assert |- -. A e. _V

  proof
    cA
    cvv
    wcel
    #
    cA
    cuni
    #
    @1
    char
    cfv
    #
    wcel
    #
    @2
    @1
    wcel
    #
    wa
    #
    @0
    @3
    @4
    @0
    @1
    con0
    wcel
    #
    @1
    @1
    cdom
    wbr
    #
    @3
    @0
    cA
    con0
    wss
    @6
    vx
    cA
    con0
    vx
    cv
    #
    cA
    wcel
    #
    @8
    con0
    wcel
    #
    vy
    cv
    @8
    csdm
    wbr
    vy
    @8
    wral
    #
    @9
    @8
    @8
    ccrd
    cfv
    #
    @8
    wceq
    #
    vx
    cab
    #
    wcel
    @13
    @10
    @11
    wa
    cA
    @14
    @8
    cardprclem.1
    eleq2i
    @13
    vx
    abid
    vy
    @8
    iscard
    3bitri
    simplbi
    ssriv
    #
    cA
    cvv
    ssonuni
    mpi
    #
    @0
    @6
    @7
    @16
    @1
    con0
    domrefg
    syl
    @1
    @1
    elharval
    sylanbrc
    cA
    @1
    @2
    vz
    cA
    @1
    vz
    cv
    #
    cA
    wcel
    #
    @17
    vw
    cv
    #
    wcel
    #
    @19
    cA
    wcel
    #
    wa
    #
    vw
    wex
    #
    @17
    @1
    wcel
    @18
    @17
    @17
    char
    cfv
    #
    wcel
    #
    @24
    cA
    wcel
    #
    @23
    @18
    @17
    con0
    wcel
    #
    @25
    cA
    con0
    @17
    @15
    sseli
    @27
    @27
    @17
    @17
    cdom
    wbr
    #
    wa
    @25
    @27
    @28
    @17
    con0
    domrefg
    ancli
    @17
    @17
    elharval
    sylibr
    syl
    @26
    @24
    ccrd
    cfv
    #
    @24
    wceq
    #
    @17
    harcard
    @13
    @30
    vx
    @24
    cA
    @17
    char
    fvex
    #
    @8
    @24
    wceq
    #
    @12
    @29
    @8
    @24
    @8
    @24
    ccrd
    fveq2
    @32
    id
    eqeq12d
    cardprclem.1
    elab2
    mpbir
    @22
    @25
    @26
    wa
    vw
    @24
    @31
    @19
    @24
    wceq
    @20
    @25
    @21
    @26
    @19
    @24
    @17
    eleq2
    @19
    @24
    cA
    eleq1
    anbi12d
    spcev
    sylancl
    vw
    @17
    cA
    eluni
    sylibr
    ssriv
    @2
    cA
    wcel
    @2
    ccrd
    cfv
    #
    @2
    wceq
    #
    @1
    harcard
    @13
    @34
    vx
    @2
    cA
    @1
    char
    fvex
    @8
    @2
    wceq
    #
    @12
    @33
    @8
    @2
    @8
    @2
    ccrd
    fveq2
    @35
    id
    eqeq12d
    cardprclem.1
    elab2
    mpbir
    sselii
    jctir
    @0
    @6
    @1
    word
    @5
    wn
    @16
    @1
    eloni
    @1
    @2
    ordn2lp
    3syl
    pm2.65i
end
