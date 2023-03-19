include "cv.mm"
include "cvv.mm"
include "csuc.mm"
include "cmpt.mm"
include "crdg.mm"
include "com.mm"
include "cres.mm"
include "crn.mm"
include "wcel.mm"
include "wel.mm"
include "wa.mm"
include "wex.mm"
include "wi.mm"
include "wal.mm"
include "c0.mm"
include "cfv.mm"
include "wceq.mm"
include "vex.mm"
include "fr0g.mm"
include "ax-mp.mm"
include "wfn.mm"
include "frfnom.mm"
include "peano1.mm"
include "fnfvelrn.mm"
include "mp2an.mm"
include "eqeltrri.mm"
include "wrex.mm"
include "wb.mm"
include "fvelrnb.mm"
include "fvex.mm"
include "sucid.mm"
include "sucex.mm"
include "eqid.mm"
include "suceq.mm"
include "frsucmpt2.mm"
include "mpan2.mm"
include "syl5eleqr.mm"
include "eleq1.mm"
include "syl5ib.mm"
include "peano2b.mm"
include "mpan.mm"
include "sylbi.mm"
include "a1i.mm"
include "jcad.mm"
include "eleq2.mm"
include "anbi12d.mm"
include "spcev.mm"
include "syl6com.mm"
include "rexlimiv.mm"
include "ax-gen.mm"
include "cdm.mm"
include "wfun.mm"
include "fndm.mm"
include "eqeltri.mm"
include "fnfun.mm"
include "funrnex.mm"
include "mp2.mm"
include "anbi2d.mm"
include "exbidv.mm"
include "imbi12d.mm"
include "albidv.mm"

theorem inf0
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let vv: setvar v
  let vf: setvar f
  assume inf0.1: |- _om e. _V

  disjoint x y
  disjoint x z
  disjoint w x
  disjoint y z
  disjoint w y
  disjoint w z
  disjoint v x
  disjoint f x
  disjoint v y
  disjoint f y
  disjoint v z
  disjoint f z
  disjoint v w
  disjoint f w
  disjoint f v
  assert |- E. y ( x e. y /\ A. z ( z e. y -> E. w ( z e. w /\ w e. y ) ) )

  proof
    vx
    cv
    #
    vv
    cvv
    vv
    cv
    #
    csuc
    #
    cmpt
    #
    @0
    crdg
    com
    cres
    #
    crn
    #
    wcel
    #
    vz
    cv
    #
    @5
    wcel
    #
    vz
    vw
    wel
    #
    vw
    cv
    #
    @5
    wcel
    #
    wa
    #
    vw
    wex
    #
    wi
    #
    vz
    wal
    #
    vx
    vy
    wel
    #
    vz
    vy
    wel
    #
    @9
    vw
    vy
    wel
    #
    wa
    #
    vw
    wex
    #
    wi
    #
    vz
    wal
    #
    wa
    #
    vy
    wex
    c0
    @4
    cfv
    #
    @0
    @5
    @0
    cvv
    wcel
    @24
    @0
    wceq
    vx
    vex
    @0
    cvv
    @3
    fr0g
    ax-mp
    @4
    com
    wfn
    #
    c0
    com
    wcel
    @24
    @5
    wcel
    @0
    @3
    frfnom
    #
    peano1
    com
    c0
    @4
    fnfvelrn
    mp2an
    eqeltrri
    @14
    vz
    @8
    vf
    cv
    #
    @4
    cfv
    #
    @7
    wceq
    #
    vf
    com
    wrex
    #
    @13
    @25
    @8
    @30
    wb
    @26
    vf
    com
    @7
    @4
    fvelrnb
    ax-mp
    @29
    @13
    vf
    com
    @29
    @27
    com
    wcel
    #
    @7
    @27
    csuc
    #
    @4
    cfv
    #
    wcel
    #
    @33
    @5
    wcel
    #
    wa
    #
    @13
    @29
    @31
    @34
    @35
    @31
    @28
    @33
    wcel
    @29
    @34
    @31
    @28
    @28
    csuc
    #
    @33
    @28
    @27
    @4
    fvex
    #
    sucid
    @31
    @37
    cvv
    wcel
    @33
    @37
    wceq
    @28
    @38
    sucex
    vv
    vz
    @0
    @27
    @2
    @37
    @7
    csuc
    @4
    cvv
    @4
    eqid
    @7
    @1
    suceq
    @7
    @28
    suceq
    frsucmpt2
    mpan2
    syl5eleqr
    @28
    @7
    @33
    eleq1
    syl5ib
    @31
    @35
    wi
    @29
    @31
    @32
    com
    wcel
    #
    @35
    @27
    peano2b
    @25
    @39
    @35
    @26
    com
    @32
    @4
    fnfvelrn
    mpan
    sylbi
    a1i
    jcad
    @12
    @36
    vw
    @33
    @32
    @4
    fvex
    @10
    @33
    wceq
    @9
    @34
    @11
    @35
    @10
    @33
    @7
    eleq2
    @10
    @33
    @5
    eleq1
    anbi12d
    spcev
    syl6com
    rexlimiv
    sylbi
    ax-gen
    @23
    @6
    @15
    wa
    vy
    @5
    @4
    cdm
    #
    cvv
    wcel
    @4
    wfun
    #
    @5
    cvv
    wcel
    @40
    com
    cvv
    @25
    @40
    com
    wceq
    @26
    com
    @4
    fndm
    ax-mp
    inf0.1
    eqeltri
    @25
    @41
    @26
    com
    @4
    fnfun
    ax-mp
    cvv
    @4
    funrnex
    mp2
    vy
    cv
    #
    @5
    wceq
    #
    @16
    @6
    @22
    @15
    @42
    @5
    @0
    eleq2
    @43
    @21
    @14
    vz
    @43
    @17
    @8
    @20
    @13
    @42
    @5
    @7
    eleq2
    @43
    @19
    @12
    vw
    @43
    @18
    @11
    @9
    @42
    @5
    @10
    eleq2
    anbi2d
    exbidv
    imbi12d
    albidv
    anbi12d
    spcev
    mp2an
end
