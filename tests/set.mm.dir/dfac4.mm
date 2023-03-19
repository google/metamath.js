include "wac.mm"
include "cv.mm"
include "c0.mm"
include "wne.mm"
include "cfv.mm"
include "wcel.mm"
include "wi.mm"
include "wral.mm"
include "wex.mm"
include "wal.mm"
include "wfn.mm"
include "wa.mm"
include "dfac3.mm"
include "wceq.mm"
include "fveq1.mm"
include "eleq1d.mm"
include "imbi2d.mm"
include "ralbidv.mm"
include "cbvexv.mm"
include "cmpt.mm"
include "fvex.mm"
include "eqid.mm"
include "fnmpti.mm"
include "fveq2.mm"
include "fvmpt.mm"
include "ralbiia.mm"
include "anbi2i.mm"
include "mpbiran.mm"
include "crn.mm"
include "csn.mm"
include "cun.mm"
include "wf.mm"
include "cvv.mm"
include "fvrn0.mm"
include "rgenw.mm"
include "fmpt.mm"
include "mpbi.mm"
include "vex.mm"
include "rnex.mm"
include "p0ex.mm"
include "unex.mm"
include "fex2.mm"
include "mp3an.mm"
include "fneq1.mm"
include "anbi12d.mm"
include "spcev.mm"
include "sylbir.mm"
include "exlimiv.mm"
include "sylbi.mm"
include "exsimpr.mm"
include "impbii.mm"
include "albii.mm"
include "bitri.mm"

theorem dfac4
  let vx: setvar x
  let vz: setvar z
  let vf: setvar f
  let vy: setvar y
  let vw: setvar w

  disjoint f x
  disjoint f z
  disjoint x z
  disjoint f y
  disjoint f w
  disjoint x y
  disjoint w x
  disjoint y z
  disjoint w z
  disjoint w y
  assert |- ( CHOICE <-> A. x E. f ( f Fn x /\ A. z e. x ( z =/= (/) -> ( f ` z ) e. z ) ) )

  proof
    wac
    vz
    cv
    #
    c0
    wne
    #
    @0
    vf
    cv
    #
    cfv
    #
    @0
    wcel
    #
    wi
    #
    vz
    vx
    cv
    #
    wral
    #
    vf
    wex
    #
    vx
    wal
    @2
    @6
    wfn
    #
    @7
    wa
    #
    vf
    wex
    #
    vx
    wal
    vx
    vz
    vf
    dfac3
    @8
    @11
    vx
    @8
    @11
    @8
    @1
    @0
    vy
    cv
    #
    cfv
    #
    @0
    wcel
    #
    wi
    #
    vz
    @6
    wral
    #
    vy
    wex
    @11
    @7
    @16
    vf
    vy
    @2
    @12
    wceq
    #
    @5
    @15
    vz
    @6
    @17
    @4
    @14
    @1
    @17
    @3
    @13
    @0
    @0
    @2
    @12
    fveq1
    eleq1d
    imbi2d
    ralbidv
    cbvexv
    @16
    @11
    vy
    @16
    vw
    @6
    vw
    cv
    #
    @12
    cfv
    #
    cmpt
    #
    @6
    wfn
    #
    @1
    @0
    @20
    cfv
    #
    @0
    wcel
    #
    wi
    #
    vz
    @6
    wral
    #
    wa
    #
    @11
    @26
    @21
    @16
    vw
    @6
    @19
    @20
    @18
    @12
    fvex
    @20
    eqid
    #
    fnmpti
    @25
    @16
    @21
    @24
    @15
    vz
    @6
    @0
    @6
    wcel
    #
    @23
    @14
    @1
    @28
    @22
    @13
    @0
    vw
    @0
    @19
    @13
    @6
    @20
    @18
    @0
    @12
    fveq2
    @27
    @0
    @12
    fvex
    fvmpt
    eleq1d
    imbi2d
    ralbiia
    anbi2i
    mpbiran
    @10
    @26
    vf
    @20
    @6
    @12
    crn
    #
    c0
    csn
    #
    cun
    #
    @20
    wf
    #
    @6
    cvv
    wcel
    @31
    cvv
    wcel
    @20
    cvv
    wcel
    @19
    @31
    wcel
    #
    vw
    @6
    wral
    @32
    @33
    vw
    @6
    @12
    @18
    fvrn0
    rgenw
    vw
    @6
    @31
    @19
    @20
    @27
    fmpt
    mpbi
    vx
    vex
    @29
    @30
    @12
    vy
    vex
    rnex
    p0ex
    unex
    @6
    @31
    @20
    cvv
    cvv
    fex2
    mp3an
    @2
    @20
    wceq
    #
    @9
    @21
    @7
    @25
    @6
    @2
    @20
    fneq1
    @34
    @5
    @24
    vz
    @6
    @34
    @4
    @23
    @1
    @34
    @3
    @22
    @0
    @0
    @2
    @20
    fveq1
    eleq1d
    imbi2d
    ralbidv
    anbi12d
    spcev
    sylbir
    exlimiv
    sylbi
    @9
    @7
    vf
    exsimpr
    impbii
    albii
    bitri
end
