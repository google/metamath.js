include "wcel.mm"
include "cvv.mm"
include "wlim.mm"
include "ccf.mm"
include "cfv.mm"
include "cv.mm"
include "ccrd.mm"
include "wceq.mm"
include "wss.mm"
include "cuni.mm"
include "wa.mm"
include "wex.mm"
include "cab.mm"
include "cint.mm"
include "elex.mm"
include "wrex.mm"
include "wral.mm"
include "wi.mm"
include "csuc.mm"
include "limsuc.mm"
include "biimpd.mm"
include "sseq1.mm"
include "rexbidv.mm"
include "rspcv.mm"
include "vex.mm"
include "sucssel.mm"
include "ax-mp.mm"
include "reximi.mm"
include "eluni2.mm"
include "sylibr.mm"
include "syl6com.mm"
include "syl9.mm"
include "ralrimdv.mm"
include "dfss3.mm"
include "syl6ibr.mm"
include "adantr.mm"
include "uniss.mm"
include "limuni.mm"
include "sseq2d.mm"
include "syl5ibr.mm"
include "imp.mm"
include "jctird.mm"
include "eqss.mm"
include "imdistanda.mm"
include "anim2d.mm"
include "eximdv.mm"
include "ss2abdv.mm"
include "intss.mm"
include "syl.mm"
include "adantl.mm"
include "con0.mm"
include "limelon.mm"
include "cfval.mm"
include "sseqtr4d.mm"
include "cfub.mm"
include "eqimss.mm"
include "anim2i.mm"
include "eximi.mm"
include "ss2abi.mm"
include "sstri.mm"
include "jctil.mm"
include "sylan.mm"

theorem cflm
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let vz: setvar z
  let vw: setvar w
  let vv: setvar v

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint x z
  disjoint w x
  disjoint v x
  disjoint y z
  disjoint w y
  disjoint v y
  disjoint w z
  disjoint v z
  disjoint A z
  disjoint v w
  disjoint A w
  disjoint A v
  assert |- ( ( A e. B /\ Lim A ) -> ( cf ` A ) = |^| { x | E. y ( x = ( card ` y ) /\ ( y C_ A /\ A = U. y ) ) } )

  proof
    cA
    cB
    wcel
    cA
    cvv
    wcel
    #
    cA
    wlim
    #
    cA
    ccf
    cfv
    #
    vx
    cv
    vy
    cv
    #
    ccrd
    cfv
    wceq
    #
    @3
    cA
    wss
    #
    cA
    @3
    cuni
    #
    wceq
    #
    wa
    #
    wa
    #
    vy
    wex
    #
    vx
    cab
    #
    cint
    #
    wceq
    #
    cA
    cB
    elex
    @0
    @1
    wa
    #
    @2
    @12
    wss
    #
    @12
    @2
    wss
    #
    wa
    @13
    @14
    @16
    @15
    @14
    @12
    @4
    @5
    vz
    cv
    #
    vw
    cv
    #
    wss
    #
    vw
    @3
    wrex
    #
    vz
    cA
    wral
    #
    wa
    #
    wa
    #
    vy
    wex
    #
    vx
    cab
    #
    cint
    #
    @2
    @1
    @12
    @26
    wss
    #
    @0
    @1
    @25
    @11
    wss
    @27
    @1
    @24
    @10
    vx
    @1
    @23
    @9
    vy
    @1
    @22
    @8
    @4
    @1
    @5
    @21
    @7
    @1
    @5
    wa
    #
    @21
    cA
    @6
    wss
    #
    @6
    cA
    wss
    #
    wa
    @7
    @28
    @21
    @29
    @30
    @1
    @21
    @29
    wi
    @5
    @1
    @21
    vv
    cv
    #
    @6
    wcel
    #
    vv
    cA
    wral
    @29
    @1
    @21
    @32
    vv
    cA
    @1
    @31
    cA
    wcel
    #
    @31
    csuc
    #
    cA
    wcel
    #
    @21
    @32
    @1
    @33
    @35
    cA
    @31
    limsuc
    biimpd
    @35
    @21
    @34
    @18
    wss
    #
    vw
    @3
    wrex
    #
    @32
    @20
    @37
    vz
    @34
    cA
    @17
    @34
    wceq
    @19
    @36
    vw
    @3
    @17
    @34
    @18
    sseq1
    rexbidv
    rspcv
    @37
    @31
    @18
    wcel
    #
    vw
    @3
    wrex
    @32
    @36
    @38
    vw
    @3
    @31
    cvv
    wcel
    @36
    @38
    wi
    vv
    vex
    @31
    @18
    cvv
    sucssel
    ax-mp
    reximi
    vw
    @31
    @3
    eluni2
    sylibr
    syl6com
    syl9
    ralrimdv
    vv
    cA
    @6
    dfss3
    syl6ibr
    adantr
    @1
    @5
    @30
    @5
    @30
    @1
    @6
    cA
    cuni
    #
    wss
    @3
    cA
    uniss
    @1
    cA
    @39
    @6
    cA
    limuni
    sseq2d
    syl5ibr
    imp
    jctird
    cA
    @6
    eqss
    syl6ibr
    imdistanda
    anim2d
    eximdv
    ss2abdv
    @25
    @11
    intss
    syl
    adantl
    @14
    cA
    con0
    wcel
    @2
    @26
    wceq
    cA
    cvv
    limelon
    vx
    vy
    vz
    vw
    cA
    cfval
    syl
    sseqtr4d
    @2
    @4
    @5
    @29
    wa
    #
    wa
    #
    vy
    wex
    #
    vx
    cab
    #
    cint
    #
    @12
    vx
    vy
    cA
    cfub
    @11
    @43
    wss
    @44
    @12
    wss
    @10
    @42
    vx
    @9
    @41
    vy
    @8
    @40
    @4
    @7
    @29
    @5
    cA
    @6
    eqimss
    anim2i
    anim2i
    eximi
    ss2abi
    @11
    @43
    intss
    ax-mp
    sstri
    jctil
    @2
    @12
    eqss
    sylibr
    sylan
end
