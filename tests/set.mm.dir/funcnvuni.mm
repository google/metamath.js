include "cv.mm"
include "ccnv.mm"
include "wfun.mm"
include "wss.mm"
include "wo.mm"
include "wral.mm"
include "wa.mm"
include "wceq.mm"
include "wrex.mm"
include "cab.mm"
include "cuni.mm"
include "wi.mm"
include "wal.mm"
include "weq.mm"
include "cnveq.mm"
include "eqeq2d.mm"
include "cbvrexv.mm"
include "wcel.mm"
include "funeqd.mm"
include "sseq1.mm"
include "sseq2.mm"
include "orbi12d.mm"
include "ralbidv.mm"
include "anbi12d.mm"
include "rspcv.mm"
include "funeq.mm"
include "biimprcd.mm"
include "cnvss.mm"
include "orim12i.mm"
include "wb.mm"
include "sseq12.mm"
include "ancoms.mm"
include "syl5ibrcom.mm"
include "expd.mm"
include "syl6com.mm"
include "rexlimdv.mm"
include "com23.mm"
include "alrimdv.mm"
include "anim12ii.mm"
include "syl5bi.mm"
include "alrimiv.mm"
include "df-ral.mm"
include "vex.mm"
include "eqeq1.mm"
include "rexbidv.mm"
include "elab.mm"
include "ralab.mm"
include "anbi2i.mm"
include "imbi12i.mm"
include "albii.mm"
include "bitr2i.mm"
include "sylib.mm"
include "fununi.mm"
include "syl.mm"
include "ciun.mm"
include "cnvuni.mm"
include "cnvex.mm"
include "dfiun2.mm"
include "eqtri.mm"
include "funeqi.mm"
include "sylibr.mm"

theorem funcnvuni
  let cA: class A
  let vf: setvar f
  let vg: setvar g
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let vv: setvar v

  disjoint f g
  disjoint A f
  disjoint A g
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint f w
  disjoint f v
  disjoint g x
  disjoint g y
  disjoint g z
  disjoint g w
  disjoint g v
  disjoint x y
  disjoint x z
  disjoint w x
  disjoint v x
  disjoint A x
  disjoint y z
  disjoint w y
  disjoint v y
  disjoint A y
  disjoint w z
  disjoint v z
  disjoint A z
  disjoint v w
  disjoint A w
  disjoint A v
  assert |- ( A. f e. A ( Fun `' f /\ A. g e. A ( f C_ g \/ g C_ f ) ) -> Fun `' U. A )

  proof
    vf
    cv
    #
    ccnv
    #
    wfun
    #
    @0
    vg
    cv
    #
    wss
    #
    @3
    @0
    wss
    #
    wo
    #
    vg
    cA
    wral
    #
    wa
    #
    vf
    cA
    wral
    #
    vy
    cv
    #
    vx
    cv
    #
    ccnv
    #
    wceq
    #
    vx
    cA
    wrex
    #
    vy
    cab
    #
    cuni
    #
    wfun
    #
    cA
    cuni
    ccnv
    #
    wfun
    @9
    vz
    cv
    #
    wfun
    #
    @19
    vw
    cv
    #
    wss
    #
    @21
    @19
    wss
    #
    wo
    #
    vw
    @15
    wral
    #
    wa
    #
    vz
    @15
    wral
    #
    @17
    @9
    @19
    @12
    wceq
    #
    vx
    cA
    wrex
    #
    @20
    @21
    @12
    wceq
    #
    vx
    cA
    wrex
    #
    @24
    wi
    #
    vw
    wal
    #
    wa
    #
    wi
    #
    vz
    wal
    #
    @27
    @9
    @35
    vz
    @29
    @19
    vv
    cv
    #
    ccnv
    #
    wceq
    #
    vv
    cA
    wrex
    @9
    @34
    @28
    @39
    vx
    vv
    cA
    vx
    vv
    weq
    @12
    @38
    @19
    @11
    @37
    cnveq
    eqeq2d
    cbvrexv
    @9
    @39
    @34
    vv
    cA
    @37
    cA
    wcel
    @9
    @38
    wfun
    #
    @37
    @3
    wss
    #
    @3
    @37
    wss
    #
    wo
    #
    vg
    cA
    wral
    #
    wa
    #
    @39
    @34
    wi
    @8
    @45
    vf
    @37
    cA
    vf
    vv
    weq
    #
    @2
    @40
    @7
    @44
    @46
    @1
    @38
    @0
    @37
    cnveq
    funeqd
    @46
    @6
    @43
    vg
    cA
    @46
    @4
    @41
    @5
    @42
    @0
    @37
    @3
    sseq1
    @0
    @37
    @3
    sseq2
    orbi12d
    ralbidv
    anbi12d
    rspcv
    @40
    @39
    @20
    @44
    @33
    @39
    @20
    @40
    @19
    @38
    funeq
    biimprcd
    @44
    @39
    @32
    vw
    @44
    @31
    @39
    @24
    @44
    @30
    @39
    @24
    wi
    #
    vx
    cA
    @11
    cA
    wcel
    @44
    @37
    @11
    wss
    #
    @11
    @37
    wss
    #
    wo
    #
    @30
    @47
    wi
    @43
    @50
    vg
    @11
    cA
    vg
    vx
    weq
    @41
    @48
    @42
    @49
    @3
    @11
    @37
    sseq2
    @3
    @11
    @37
    sseq1
    orbi12d
    rspcv
    @50
    @30
    @39
    @24
    @50
    @24
    @30
    @39
    wa
    #
    @38
    @12
    wss
    #
    @12
    @38
    wss
    #
    wo
    @48
    @52
    @49
    @53
    @37
    @11
    cnvss
    @11
    @37
    cnvss
    orim12i
    @51
    @22
    @52
    @23
    @53
    @39
    @30
    @22
    @52
    wb
    @19
    @38
    @21
    @12
    sseq12
    ancoms
    @21
    @12
    @19
    @38
    sseq12
    orbi12d
    syl5ibrcom
    expd
    syl6com
    rexlimdv
    com23
    alrimdv
    anim12ii
    syl6com
    rexlimdv
    syl5bi
    alrimiv
    @27
    @19
    @15
    wcel
    #
    @26
    wi
    #
    vz
    wal
    @36
    @26
    vz
    @15
    df-ral
    @55
    @35
    vz
    @54
    @29
    @26
    @34
    @14
    @29
    vy
    @19
    vz
    vex
    vy
    vz
    weq
    @13
    @28
    vx
    cA
    @10
    @19
    @12
    eqeq1
    rexbidv
    elab
    @25
    @33
    @20
    @14
    @31
    @24
    vw
    vy
    vy
    vw
    weq
    @13
    @30
    vx
    cA
    @10
    @21
    @12
    eqeq1
    rexbidv
    ralab
    anbi2i
    imbi12i
    albii
    bitr2i
    sylib
    @15
    vz
    vw
    fununi
    syl
    @18
    @16
    @18
    vx
    cA
    @12
    ciun
    @16
    vx
    cA
    cnvuni
    vx
    vy
    cA
    @12
    @11
    vx
    vex
    cnvex
    dfiun2
    eqtri
    funeqi
    sylibr
end
