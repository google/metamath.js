include "wfun.mm"
include "cop.mm"
include "wceq.mm"
include "cv.mm"
include "csn.mm"
include "wa.mm"
include "wex.mm"
include "cdm.mm"
include "cfv.mm"
include "ciun.mm"
include "wi.mm"
include "funiun.mm"
include "wb.mm"
include "eqeq1.mm"
include "eqcom.mm"
include "syl6bb.mm"
include "adantl.mm"
include "c0.mm"
include "wne.mm"
include "opnzi.mm"
include "neeq1.mm"
include "eqcoms.mm"
include "wrel.mm"
include "funrel.mm"
include "reldm0.mm"
include "syl.mm"
include "biimprd.mm"
include "necon3d.mm"
include "com12.mm"
include "syl6bi.mm"
include "com3l.mm"
include "impd.mm"
include "ax-mp.mm"
include "fvex.mm"
include "iunopeqop.mm"
include "sylbid.mm"
include "imp.mm"
include "iuneq1.mm"
include "vex.mm"
include "weq.mm"
include "id.mm"
include "fveq2.mm"
include "opeq12d.mm"
include "sneqd.mm"
include "iunxsn.mm"
include "syl6eq.mm"
include "eqeq2d.mm"
include "w3a.mm"
include "snopeqop.mm"
include "sylbb.mm"
include "simpr3.mm"
include "simp1.mm"
include "eqcomd.mm"
include "opeq2d.mm"
include "biimpac.mm"
include "jca.mm"
include "ex.mm"
include "a1dd.mm"
include "mpd.mm"
include "impancom.mm"
include "eximdv.mm"
include "expcom.mm"
include "expd.mm"
include "mpcom.mm"

theorem funopsn
  let cF: class F
  let cX: class X
  let cY: class Y
  let va: setvar a
  let vx: setvar x
  assume funopsn.x: |- X e. _V
  assume funopsn.y: |- Y e. _V

  disjoint F a
  disjoint X a
  disjoint Y a
  disjoint F x
  disjoint a x
  disjoint X x
  disjoint Y x
  assert |- ( ( Fun F /\ F = <. X , Y >. ) -> E. a ( X = { a } /\ F = { <. a , a >. } ) )

  proof
    cF
    wfun
    #
    cF
    cX
    cY
    cop
    #
    wceq
    #
    cX
    va
    cv
    #
    csn
    #
    wceq
    #
    cF
    @3
    @3
    cop
    #
    csn
    #
    wceq
    #
    wa
    #
    va
    wex
    #
    cF
    vx
    cF
    cdm
    #
    vx
    cv
    #
    @12
    cF
    cfv
    #
    cop
    #
    csn
    #
    ciun
    #
    wceq
    #
    @0
    @2
    @10
    wi
    vx
    cF
    funiun
    @17
    @0
    @2
    @10
    @0
    @2
    wa
    #
    @17
    @10
    @18
    @17
    wa
    #
    @11
    @4
    wceq
    #
    va
    wex
    #
    @10
    @18
    @17
    @21
    @18
    @17
    @16
    @1
    wceq
    #
    @21
    @2
    @17
    @22
    wb
    @0
    @2
    @17
    @1
    @16
    wceq
    @22
    cF
    @1
    @16
    eqeq1
    @1
    @16
    eqcom
    syl6bb
    adantl
    @18
    @11
    c0
    wne
    #
    @22
    @21
    wi
    @1
    c0
    wne
    #
    @18
    @23
    wi
    cX
    cY
    funopsn.x
    funopsn.y
    opnzi
    @24
    @0
    @2
    @23
    @2
    @24
    @0
    @23
    @2
    @24
    cF
    c0
    wne
    #
    @0
    @23
    wi
    @24
    @25
    wb
    @1
    cF
    @1
    cF
    c0
    neeq1
    eqcoms
    @0
    @25
    @23
    @0
    @11
    c0
    cF
    c0
    @0
    cF
    c0
    wceq
    #
    @11
    c0
    wceq
    #
    @0
    cF
    wrel
    @26
    @27
    wb
    cF
    funrel
    cF
    reldm0
    syl
    biimprd
    necon3d
    com12
    syl6bi
    com3l
    impd
    ax-mp
    vx
    va
    @11
    @13
    cX
    cY
    @12
    cF
    fvex
    funopsn.x
    funopsn.y
    iunopeqop
    syl
    sylbid
    imp
    @19
    @20
    @9
    va
    @18
    @20
    @17
    @9
    @18
    @20
    wa
    #
    @17
    cF
    @3
    @3
    cF
    cfv
    #
    cop
    #
    csn
    #
    wceq
    #
    @9
    @28
    @16
    @31
    cF
    @20
    @16
    @31
    wceq
    @18
    @20
    @16
    vx
    @4
    @15
    ciun
    @31
    vx
    @11
    @4
    @15
    iuneq1
    vx
    @3
    @15
    @31
    va
    vex
    #
    vx
    va
    weq
    #
    @14
    @30
    @34
    @12
    @3
    @13
    @29
    @34
    id
    @12
    @3
    cF
    fveq2
    opeq12d
    sneqd
    iunxsn
    syl6eq
    adantl
    eqeq2d
    @18
    @32
    @20
    @9
    @18
    @32
    wa
    #
    @3
    @29
    wceq
    #
    cX
    cY
    wceq
    #
    @5
    w3a
    #
    @20
    @9
    wi
    @18
    @32
    @38
    @18
    @32
    @1
    @31
    wceq
    #
    @38
    @2
    @32
    @39
    wb
    @0
    cF
    @1
    @31
    eqeq1
    adantl
    @39
    @31
    @1
    wceq
    @38
    @1
    @31
    eqcom
    @3
    @29
    cX
    cY
    @33
    @3
    cF
    fvex
    funopsn.x
    funopsn.y
    snopeqop
    sylbb
    syl6bi
    imp
    @35
    @38
    @9
    @20
    @32
    @38
    @9
    wi
    @18
    @32
    @38
    @9
    @32
    @38
    wa
    @5
    @8
    @32
    @36
    @37
    @5
    simpr3
    @38
    @32
    @8
    @38
    @31
    @7
    cF
    @38
    @30
    @6
    @38
    @29
    @3
    @3
    @38
    @3
    @29
    @36
    @37
    @5
    simp1
    eqcomd
    opeq2d
    sneqd
    eqeq2d
    biimpac
    jca
    ex
    adantl
    a1dd
    mpd
    impancom
    sylbid
    impancom
    eximdv
    mpd
    expcom
    expd
    mpcom
    imp
end
