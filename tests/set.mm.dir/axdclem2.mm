include "cv.mm"
include "c0.mm"
include "wne.mm"
include "cfv.mm"
include "wcel.mm"
include "wi.mm"
include "cdm.mm"
include "cpw.mm"
include "wral.mm"
include "wbr.mm"
include "wex.mm"
include "crn.mm"
include "wss.mm"
include "csuc.mm"
include "com.mm"
include "w3a.mm"
include "cvv.mm"
include "wf.mm"
include "wfn.mm"
include "cab.mm"
include "cmpt.mm"
include "crdg.mm"
include "cres.mm"
include "frfnom.mm"
include "fneq1i.mm"
include "mpbir.mm"
include "a1i.mm"
include "wceq.mm"
include "fveq2.mm"
include "suceq.mm"
include "fveq2d.mm"
include "breq12d.mm"
include "fveq1i.mm"
include "vex.mm"
include "fr0g.mm"
include "ax-mp.mm"
include "eqtri.mm"
include "breq1i.mm"
include "biimpri.mm"
include "eximi.mm"
include "peano1.mm"
include "axdclem.mm"
include "mpi.mm"
include "syl3an3.mm"
include "3com23.mm"
include "wa.mm"
include "fvex.mm"
include "brelrn.mm"
include "ssel.mm"
include "syl5.mm"
include "eldm.mm"
include "syl6ib.mm"
include "ad2antll.mm"
include "peano2.mm"
include "3expia.mm"
include "com3r.mm"
include "imp.mm"
include "syld.mm"
include "3adantr2.mm"
include "ex.mm"
include "finds2.mm"
include "com12.mm"
include "breldm.mm"
include "syl6.mm"
include "ralrimiv.mm"
include "ffnfv.mm"
include "sylanbrc.mm"
include "omex.mm"
include "dmex.mm"
include "fex2.mm"
include "syl3anc.mm"
include "fveq1.mm"
include "ralbidv.mm"
include "spcegv.mm"
include "sylc.mm"
include "3exp.mm"
include "pwex.mm"
include "ac4c.mm"
include "exlimiiv.mm"

theorem axdclem2
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vf: setvar f
  let vg: setvar g
  let vn: setvar n
  let cF: class F
  let vs: setvar s
  let vk: setvar k
  assume axdclem2.1: |- F = ( rec ( ( y e. _V |-> ( g ` { z | y x z } ) ) , s ) |` _om )

  disjoint F f
  disjoint F n
  disjoint f n
  disjoint F y
  disjoint F z
  disjoint n y
  disjoint n z
  disjoint y z
  disjoint f g
  disjoint f x
  disjoint g n
  disjoint g x
  disjoint n x
  disjoint g s
  disjoint g y
  disjoint n s
  disjoint s y
  disjoint g z
  disjoint x y
  disjoint x z
  disjoint F k
  disjoint k n
  disjoint k y
  disjoint k z
  disjoint g k
  disjoint k s
  disjoint k x
  assert |- ( E. z s x z -> ( ran x C_ dom x -> E. f A. n e. _om ( f ` n ) x ( f ` suc n ) ) )

  proof
    vy
    cv
    #
    c0
    wne
    @0
    vg
    cv
    #
    cfv
    @0
    wcel
    wi
    vy
    vx
    cv
    #
    cdm
    #
    cpw
    #
    wral
    #
    vs
    cv
    #
    vz
    cv
    #
    @2
    wbr
    #
    vz
    wex
    #
    @2
    crn
    #
    @3
    wss
    #
    vn
    cv
    #
    vf
    cv
    #
    cfv
    #
    @12
    csuc
    #
    @13
    cfv
    #
    @2
    wbr
    #
    vn
    com
    wral
    #
    vf
    wex
    #
    wi
    wi
    vg
    @5
    @9
    @11
    @19
    @5
    @9
    @11
    w3a
    #
    cF
    cvv
    wcel
    #
    @12
    cF
    cfv
    #
    @15
    cF
    cfv
    #
    @2
    wbr
    #
    vn
    com
    wral
    #
    @19
    @20
    com
    @3
    cF
    wf
    #
    com
    cvv
    wcel
    #
    @3
    cvv
    wcel
    #
    @21
    @20
    cF
    com
    wfn
    #
    @22
    @3
    wcel
    #
    vn
    com
    wral
    @26
    @29
    @20
    @29
    vy
    cvv
    @0
    @7
    @2
    wbr
    vz
    cab
    @1
    cfv
    cmpt
    #
    @6
    crdg
    com
    cres
    #
    com
    wfn
    @6
    @31
    frfnom
    com
    cF
    @32
    axdclem2.1
    fneq1i
    mpbir
    a1i
    @20
    @30
    vn
    com
    @20
    @12
    com
    wcel
    #
    @24
    @30
    @33
    @20
    @24
    @24
    c0
    cF
    cfv
    #
    c0
    csuc
    #
    cF
    cfv
    #
    @2
    wbr
    #
    vk
    cv
    #
    cF
    cfv
    #
    @38
    csuc
    #
    cF
    cfv
    #
    @2
    wbr
    #
    @41
    @40
    csuc
    #
    cF
    cfv
    #
    @2
    wbr
    #
    @20
    vn
    vk
    @12
    c0
    wceq
    #
    @22
    @34
    @23
    @36
    @2
    @12
    c0
    cF
    fveq2
    @46
    @15
    @35
    cF
    @12
    c0
    suceq
    fveq2d
    breq12d
    @12
    @38
    wceq
    #
    @22
    @39
    @23
    @41
    @2
    @12
    @38
    cF
    fveq2
    @47
    @15
    @40
    cF
    @12
    @38
    suceq
    fveq2d
    breq12d
    @12
    @40
    wceq
    #
    @22
    @41
    @23
    @44
    @2
    @12
    @40
    cF
    fveq2
    @48
    @15
    @43
    cF
    @12
    @40
    suceq
    fveq2d
    breq12d
    @5
    @11
    @9
    @37
    @9
    @5
    @11
    @34
    @7
    @2
    wbr
    #
    vz
    wex
    #
    @37
    @8
    @49
    vz
    @49
    @8
    @34
    @6
    @7
    @2
    @34
    c0
    @32
    cfv
    #
    @6
    c0
    cF
    @32
    axdclem2.1
    fveq1i
    @6
    cvv
    wcel
    @51
    @6
    wceq
    vs
    vex
    @6
    cvv
    @31
    fr0g
    ax-mp
    eqtri
    breq1i
    biimpri
    eximi
    @5
    @11
    @50
    w3a
    c0
    com
    wcel
    @37
    peano1
    vx
    vy
    vz
    vg
    cF
    c0
    vs
    axdclem2.1
    axdclem
    mpi
    syl3an3
    3com23
    @38
    com
    wcel
    #
    @20
    @42
    @45
    wi
    #
    @52
    @5
    @11
    @53
    @9
    @52
    @5
    @11
    wa
    #
    wa
    @42
    @41
    @7
    @2
    wbr
    vz
    wex
    #
    @45
    @11
    @42
    @55
    wi
    @52
    @5
    @11
    @42
    @41
    @3
    wcel
    #
    @55
    @42
    @41
    @10
    wcel
    @11
    @56
    @39
    @41
    @2
    @38
    cF
    fvex
    @40
    cF
    fvex
    #
    brelrn
    @10
    @3
    @41
    ssel
    syl5
    vz
    @41
    @2
    @57
    eldm
    syl6ib
    ad2antll
    @52
    @54
    @55
    @45
    wi
    @54
    @55
    @52
    @45
    @5
    @11
    @55
    @52
    @45
    wi
    @52
    @40
    com
    wcel
    @5
    @11
    @55
    w3a
    @45
    @38
    peano2
    vx
    vy
    vz
    vg
    cF
    @40
    vs
    axdclem2.1
    axdclem
    syl5
    3expia
    com3r
    imp
    syld
    3adantr2
    ex
    finds2
    com12
    #
    @22
    @23
    @2
    @12
    cF
    fvex
    @15
    cF
    fvex
    breldm
    syl6
    ralrimiv
    vn
    com
    @3
    cF
    ffnfv
    sylanbrc
    @27
    @20
    omex
    a1i
    @28
    @20
    @2
    vx
    vex
    dmex
    #
    a1i
    com
    @3
    cF
    cvv
    cvv
    fex2
    syl3anc
    @20
    @24
    vn
    com
    @58
    ralrimiv
    @18
    @25
    vf
    cF
    cvv
    @13
    cF
    wceq
    #
    @17
    @24
    vn
    com
    @60
    @14
    @22
    @16
    @23
    @2
    @12
    @13
    cF
    fveq1
    @15
    @13
    cF
    fveq1
    breq12d
    ralbidv
    spcegv
    sylc
    3exp
    vy
    @4
    vg
    @3
    @59
    pwex
    ac4c
    exlimiiv
end
