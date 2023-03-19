include "cimage.mm"
include "csingle.mm"
include "ccom.mm"
include "cvv.mm"
include "csingles.mm"
include "cxp.mm"
include "cin.mm"
include "cdm.mm"
include "wcel.mm"
include "csn.mm"
include "cima.mm"
include "cv.mm"
include "wceq.mm"
include "wex.mm"
include "elex.mm"
include "vsnid.mm"
include "eleq2.mm"
include "mpbiri.mm"
include "c0.mm"
include "n0i.mm"
include "wn.mm"
include "snprc.mm"
include "biimpi.mm"
include "imaeq2d.mm"
include "ima0.mm"
include "syl6eq.mm"
include "nsyl2.mm"
include "syl.mm"
include "exlimiv.mm"
include "eleq1.mm"
include "sneq.mm"
include "eqeq1d.mm"
include "exbidv.mm"
include "wbr.mm"
include "wa.mm"
include "vex.mm"
include "eldm.mm"
include "brxp.mm"
include "mpbiran.mm"
include "elsingles.mm"
include "bitri.mm"
include "anbi2i.mm"
include "brin.mm"
include "19.42v.mm"
include "3bitr4i.mm"
include "exbii.mm"
include "excom.mm"
include "exancom.mm"
include "snex.mm"
include "breq2.mm"
include "ceqsexv.mm"
include "brco.mm"
include "brsingle.mm"
include "anbi1i.mm"
include "breq1.mm"
include "brimage.mm"
include "eqcom.mm"
include "3bitri.mm"
include "vtoclbg.mm"
include "pm5.21nii.mm"

theorem funpartlem
  let vx: setvar x
  let cA: class A
  let cF: class F
  let vy: setvar y
  let vz: setvar z

  disjoint A x
  disjoint F x
  disjoint A y
  disjoint A z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint F y
  disjoint F z
  assert |- ( A e. dom ( ( Image F o. Singleton ) i^i ( _V X. Singletons ) ) <-> E. x ( F " { A } ) = { x } )

  proof
    cA
    cF
    cimage
    #
    csingle
    ccom
    #
    cvv
    csingles
    cxp
    #
    cin
    #
    cdm
    #
    wcel
    #
    cA
    cvv
    wcel
    #
    cF
    cA
    csn
    #
    cima
    #
    vx
    cv
    #
    csn
    #
    wceq
    #
    vx
    wex
    #
    cA
    @4
    elex
    @11
    @6
    vx
    @11
    @9
    @8
    wcel
    #
    @6
    @11
    @13
    @9
    @10
    wcel
    vx
    vsnid
    @8
    @10
    @9
    eleq2
    mpbiri
    @13
    @8
    c0
    wceq
    @6
    @8
    @9
    n0i
    @6
    wn
    #
    @8
    cF
    c0
    cima
    c0
    @14
    @7
    c0
    cF
    @14
    @7
    c0
    wceq
    cA
    snprc
    biimpi
    imaeq2d
    cF
    ima0
    syl6eq
    nsyl2
    syl
    exlimiv
    vy
    cv
    #
    @4
    wcel
    #
    cF
    @15
    csn
    #
    cima
    #
    @10
    wceq
    #
    vx
    wex
    #
    @5
    @12
    vy
    cA
    cvv
    @15
    cA
    @4
    eleq1
    @15
    cA
    wceq
    #
    @19
    @11
    vx
    @21
    @18
    @8
    @10
    @21
    @17
    @7
    cF
    @15
    cA
    sneq
    imaeq2d
    eqeq1d
    exbidv
    @16
    @15
    vz
    cv
    #
    @3
    wbr
    #
    vz
    wex
    #
    @15
    @22
    @1
    wbr
    #
    @22
    @10
    wceq
    #
    wa
    #
    vz
    wex
    #
    vx
    wex
    #
    @20
    vz
    @15
    @3
    vy
    vex
    #
    eldm
    @24
    @27
    vx
    wex
    #
    vz
    wex
    @29
    @23
    @31
    vz
    @25
    @15
    @22
    @2
    wbr
    #
    wa
    @25
    @26
    vx
    wex
    #
    wa
    @23
    @31
    @32
    @33
    @25
    @32
    @22
    csingles
    wcel
    #
    @33
    @32
    @15
    cvv
    wcel
    @34
    @30
    @15
    @22
    cvv
    csingles
    brxp
    mpbiran
    vx
    @22
    elsingles
    bitri
    anbi2i
    @15
    @22
    @1
    @2
    brin
    @25
    @26
    vx
    19.42v
    3bitr4i
    exbii
    @27
    vz
    vx
    excom
    bitri
    @28
    @19
    vx
    @28
    @26
    @25
    wa
    vz
    wex
    @15
    @10
    @1
    wbr
    #
    @19
    @25
    @26
    vz
    exancom
    @25
    @35
    vz
    @10
    @9
    snex
    #
    @22
    @10
    @15
    @1
    breq2
    ceqsexv
    @35
    @15
    @22
    csingle
    wbr
    #
    @22
    @10
    @0
    wbr
    #
    wa
    #
    vz
    wex
    @22
    @17
    wceq
    #
    @38
    wa
    #
    vz
    wex
    #
    @19
    vz
    @15
    @10
    @0
    csingle
    @30
    @36
    brco
    @39
    @41
    vz
    @37
    @40
    @38
    @15
    @22
    @30
    vz
    vex
    brsingle
    anbi1i
    exbii
    @42
    @17
    @10
    @0
    wbr
    #
    @10
    @18
    wceq
    @19
    @38
    @43
    vz
    @17
    @15
    snex
    #
    @22
    @17
    @10
    @0
    breq1
    ceqsexv
    @17
    @10
    cF
    @44
    @36
    brimage
    @10
    @18
    eqcom
    3bitri
    3bitri
    3bitri
    exbii
    3bitri
    vtoclbg
    pm5.21nii
end
