include "wac.mm"
include "cv.mm"
include "wacn.mm"
include "cvv.mm"
include "wceq.mm"
include "wal.mm"
include "wcel.mm"
include "vex.mm"
include "acacni.mm"
include "mpan2.mm"
include "alrimiv.mm"
include "wfn.mm"
include "c0.mm"
include "wne.mm"
include "cfv.mm"
include "wi.mm"
include "wral.mm"
include "wa.mm"
include "wex.mm"
include "csn.mm"
include "cdif.mm"
include "cuni.mm"
include "wf.mm"
include "difexg.mm"
include "ax-mp.mm"
include "acneq.mm"
include "eqeq1d.mm"
include "spcv.mm"
include "wss.mm"
include "vuniex.mm"
include "id.mm"
include "syl5eleqr.mm"
include "eldifi.mm"
include "elssuni.mm"
include "syl.mm"
include "eldifsni.mm"
include "jca.mm"
include "rgen.mm"
include "acni2.mm"
include "sylancl.mm"
include "cmpt.mm"
include "mptex.mm"
include "simpr.mm"
include "eldifsn.mm"
include "imbi1i.mm"
include "fveq2.mm"
include "eqid.mm"
include "fvex.mm"
include "fvmpt.mm"
include "eleq1d.mm"
include "pm5.74i.mm"
include "impexp.mm"
include "3bitr3i.mm"
include "ralbii2.mm"
include "sylib.mm"
include "crn.mm"
include "cun.mm"
include "fvrn0.mm"
include "rgenw.mm"
include "fmpt.mm"
include "mpbi.mm"
include "ffn.mm"
include "jctil.mm"
include "fneq1.mm"
include "fveq1.mm"
include "imbi2d.mm"
include "ralbidv.mm"
include "anbi12d.mm"
include "spcegv.mm"
include "mpsyl.mm"
include "exlimiv.mm"
include "3syl.mm"
include "dfac4.mm"
include "sylibr.mm"
include "impbii.mm"

theorem dfacacn
  let vx: setvar x
  let vf: setvar f
  let vg: setvar g
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cV: class V


  assert |- ( CHOICE <-> A. x AC_ x = _V )

  proof
    wac
    vx
    cv
    #
    wacn
    #
    cvv
    wceq
    #
    vx
    wal
    #
    wac
    @2
    vx
    wac
    @0
    cvv
    wcel
    @2
    vx
    vex
    @0
    cvv
    acacni
    mpan2
    alrimiv
    @3
    vf
    cv
    #
    vy
    cv
    #
    wfn
    #
    vz
    cv
    #
    c0
    wne
    #
    @7
    @4
    cfv
    #
    @7
    wcel
    #
    wi
    #
    vz
    @5
    wral
    #
    wa
    #
    vf
    wex
    #
    vy
    wal
    wac
    @3
    @14
    vy
    @3
    @5
    c0
    csn
    #
    cdif
    #
    wacn
    #
    cvv
    wceq
    #
    @16
    @5
    cuni
    #
    vg
    cv
    #
    wf
    #
    @7
    @20
    cfv
    #
    @7
    wcel
    #
    vz
    @16
    wral
    #
    wa
    #
    vg
    wex
    #
    @14
    @2
    @18
    vx
    @16
    @5
    cvv
    wcel
    @16
    cvv
    wcel
    vy
    vex
    #
    @5
    @15
    cvv
    difexg
    ax-mp
    @0
    @16
    wceq
    @1
    @17
    cvv
    @0
    @16
    acneq
    eqeq1d
    spcv
    @18
    @19
    @17
    wcel
    @7
    @19
    wss
    #
    @8
    wa
    #
    vz
    @16
    wral
    @26
    @18
    @19
    cvv
    @17
    vy
    vuniex
    @18
    id
    syl5eleqr
    @29
    vz
    @16
    @7
    @16
    wcel
    #
    @28
    @8
    @30
    @7
    @5
    wcel
    #
    @28
    @7
    @5
    @15
    eldifi
    #
    @7
    @5
    elssuni
    syl
    @7
    @5
    c0
    eldifsni
    jca
    rgen
    vz
    @16
    @7
    vg
    @19
    acni2
    sylancl
    @25
    @14
    vg
    vx
    @5
    @0
    @20
    cfv
    #
    cmpt
    #
    cvv
    wcel
    @25
    @34
    @5
    wfn
    #
    @8
    @7
    @34
    cfv
    #
    @7
    wcel
    #
    wi
    #
    vz
    @5
    wral
    #
    wa
    #
    @14
    vx
    @5
    @33
    @27
    mptex
    @25
    @39
    @35
    @25
    @24
    @39
    @21
    @24
    simpr
    @23
    @38
    vz
    @16
    @5
    @30
    @37
    wi
    @31
    @8
    wa
    #
    @37
    wi
    @30
    @23
    wi
    @31
    @38
    wi
    @30
    @41
    @37
    @7
    @5
    c0
    eldifsn
    imbi1i
    @30
    @37
    @23
    @30
    @36
    @22
    @7
    @30
    @31
    @36
    @22
    wceq
    @32
    vx
    @7
    @33
    @22
    @5
    @34
    @0
    @7
    @20
    fveq2
    @34
    eqid
    #
    @7
    @20
    fvex
    fvmpt
    syl
    eleq1d
    pm5.74i
    @31
    @8
    @37
    impexp
    3bitr3i
    ralbii2
    sylib
    @5
    @20
    crn
    @15
    cun
    #
    @34
    wf
    #
    @35
    @33
    @43
    wcel
    #
    vx
    @5
    wral
    @44
    @45
    vx
    @5
    @20
    @0
    fvrn0
    rgenw
    vx
    @5
    @43
    @33
    @34
    @42
    fmpt
    mpbi
    @5
    @43
    @34
    ffn
    ax-mp
    jctil
    @13
    @40
    vf
    @34
    cvv
    @4
    @34
    wceq
    #
    @6
    @35
    @12
    @39
    @5
    @4
    @34
    fneq1
    @46
    @11
    @38
    vz
    @5
    @46
    @10
    @37
    @8
    @46
    @9
    @36
    @7
    @7
    @4
    @34
    fveq1
    eleq1d
    imbi2d
    ralbidv
    anbi12d
    spcegv
    mpsyl
    exlimiv
    3syl
    alrimiv
    vy
    vz
    vf
    dfac4
    sylibr
    impbii
end
