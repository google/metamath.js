include "cv.mm"
include "csn.mm"
include "cxp.mm"
include "cin.mm"
include "wcel.mm"
include "weu.mm"
include "cop.mm"
include "wceq.mm"
include "wa.mm"
include "wex.mm"
include "elin.mm"
include "elxp.mm"
include "excom.mm"
include "bitri.mm"
include "anbi1i.mm"
include "19.41vv.mm"
include "an32.mm"
include "eleq1.mm"
include "pm5.32i.mm"
include "velsn.mm"
include "anbi12i.mm"
include "an4.mm"
include "ancom.mm"
include "anass.mm"
include "3bitri.mm"
include "exbii.mm"
include "vex.mm"
include "opeq1.mm"
include "eqeq2d.mm"
include "eleq1d.mm"
include "anbi2d.mm"
include "anbi12d.mm"
include "ceqsexv.mm"
include "bitr3i.mm"
include "eubii.mm"
include "euop2.mm"

theorem dfac5lem1
  let vy: setvar y
  let vw: setvar w
  let vv: setvar v
  let vg: setvar g
  let vt: setvar t

  disjoint v w
  disjoint v y
  disjoint g v
  disjoint w y
  disjoint g w
  disjoint g y
  disjoint t v
  disjoint t w
  disjoint t y
  disjoint g t
  assert |- ( E! v v e. ( ( { w } X. w ) i^i y ) <-> E! g ( g e. w /\ <. w , g >. e. y ) )

  proof
    vv
    cv
    #
    vw
    cv
    #
    csn
    #
    @1
    cxp
    #
    vy
    cv
    #
    cin
    wcel
    #
    vv
    weu
    @0
    @1
    vg
    cv
    #
    cop
    #
    wceq
    #
    @6
    @1
    wcel
    #
    @7
    @4
    wcel
    #
    wa
    #
    wa
    #
    vg
    wex
    #
    vv
    weu
    @11
    vg
    weu
    @5
    @13
    vv
    @5
    @0
    @3
    wcel
    #
    @0
    @4
    wcel
    #
    wa
    @0
    vt
    cv
    #
    @6
    cop
    #
    wceq
    #
    @16
    @2
    wcel
    #
    @9
    wa
    #
    wa
    #
    vt
    wex
    vg
    wex
    #
    @15
    wa
    #
    @13
    @0
    @3
    @4
    elin
    @14
    @22
    @15
    @14
    @21
    vg
    wex
    vt
    wex
    @22
    vt
    vg
    @0
    @2
    @1
    elxp
    @21
    vt
    vg
    excom
    bitri
    anbi1i
    @23
    @21
    @15
    wa
    #
    vt
    wex
    #
    vg
    wex
    @13
    @21
    @15
    vg
    vt
    19.41vv
    @25
    @12
    vg
    @25
    @16
    @1
    wceq
    #
    @18
    @9
    @17
    @4
    wcel
    #
    wa
    #
    wa
    #
    wa
    #
    vt
    wex
    @12
    @24
    @30
    vt
    @24
    @18
    @15
    wa
    #
    @20
    wa
    @18
    @27
    wa
    #
    @26
    @9
    wa
    #
    wa
    #
    @30
    @18
    @20
    @15
    an32
    @31
    @32
    @20
    @33
    @18
    @15
    @27
    @0
    @17
    @4
    eleq1
    pm5.32i
    @19
    @26
    @9
    vt
    @1
    velsn
    anbi1i
    anbi12i
    @34
    @18
    @26
    wa
    #
    @27
    @9
    wa
    #
    wa
    @26
    @18
    wa
    #
    @28
    wa
    @30
    @18
    @27
    @26
    @9
    an4
    @35
    @37
    @36
    @28
    @18
    @26
    ancom
    @27
    @9
    ancom
    anbi12i
    @26
    @18
    @28
    anass
    3bitri
    3bitri
    exbii
    @29
    @12
    vt
    @1
    vw
    vex
    #
    @26
    @18
    @8
    @28
    @11
    @26
    @17
    @7
    @0
    @16
    @1
    @6
    opeq1
    #
    eqeq2d
    @26
    @27
    @10
    @9
    @26
    @17
    @7
    @4
    @39
    eleq1d
    anbi2d
    anbi12d
    ceqsexv
    bitri
    exbii
    bitr3i
    3bitri
    eubii
    @11
    vv
    vg
    @1
    @38
    euop2
    bitri
end
