include "wcel.mm"
include "cv.mm"
include "ciedg.mm"
include "cfv.mm"
include "cdm.mm"
include "cword.mm"
include "cc0.mm"
include "chash.mm"
include "cfz.mm"
include "co.mm"
include "cvtx.mm"
include "wf.mm"
include "c1.mm"
include "caddc.mm"
include "wceq.mm"
include "csn.mm"
include "cpr.mm"
include "wss.mm"
include "wif.mm"
include "cfzo.mm"
include "wral.mm"
include "w3a.mm"
include "copab.mm"
include "cvv.mm"
include "cwlks.mm"
include "cmpt.mm"
include "df-wlks.mm"
include "a1i.mm"
include "fveq2.mm"
include "syl6eqr.mm"
include "dmeqd.mm"
include "wrdeq.mm"
include "syl.mm"
include "eleq2d.mm"
include "feq3d.mm"
include "biidd.mm"
include "fveq1d.mm"
include "eqeq1d.mm"
include "sseq2d.mm"
include "ifpbi123d.mm"
include "ralbidv.mm"
include "3anbi123d.mm"
include "opabbidv.mm"
include "adantl.mm"
include "elex.mm"
include "wa.mm"
include "3anass.mm"
include "opabbii.mm"
include "fvex.mm"
include "eqeltri.mm"
include "dmex.mm"
include "wrdexg.mm"
include "mp1i.mm"
include "cab.mm"
include "ovex.mm"
include "mapex.mm"
include "sylancr.mm"
include "simpl.mm"
include "ss2abi.mm"
include "ssexd.mm"
include "opabex3d.mm"
include "syl5eqel.mm"
include "fvmptd.mm"

theorem wksfval
  let vf: setvar f
  let vk: setvar k
  let cG: class G
  let cI: class I
  let cV: class V
  let cW: class W
  let vp: setvar p
  let vg: setvar g
  assume wksfval.v: |- V = ( Vtx ` G )
  assume wksfval.i: |- I = ( iEdg ` G )

  disjoint G f
  disjoint G k
  disjoint G p
  disjoint f k
  disjoint f p
  disjoint k p
  disjoint I f
  disjoint I p
  disjoint V p
  disjoint W f
  disjoint G g
  disjoint f g
  disjoint g k
  disjoint g p
  disjoint I g
  disjoint V g
  disjoint W g
  assert |- ( G e. W -> ( Walks ` G ) = { <. f , p >. | ( f e. Word dom I /\ p : ( 0 ... ( # ` f ) ) --> V /\ A. k e. ( 0 ..^ ( # ` f ) ) if- ( ( p ` k ) = ( p ` ( k + 1 ) ) , ( I ` ( f ` k ) ) = { ( p ` k ) } , { ( p ` k ) , ( p ` ( k + 1 ) ) } C_ ( I ` ( f ` k ) ) ) ) } )

  proof
    cG
    cW
    wcel
    #
    vg
    cG
    vf
    cv
    #
    vg
    cv
    #
    ciedg
    cfv
    #
    cdm
    #
    cword
    #
    wcel
    #
    cc0
    @1
    chash
    cfv
    #
    cfz
    co
    #
    @2
    cvtx
    cfv
    #
    vp
    cv
    #
    wf
    #
    vk
    cv
    #
    @10
    cfv
    #
    @12
    c1
    caddc
    co
    @10
    cfv
    #
    wceq
    #
    @12
    @1
    cfv
    #
    @3
    cfv
    #
    @13
    csn
    #
    wceq
    #
    @13
    @14
    cpr
    #
    @17
    wss
    #
    wif
    #
    vk
    cc0
    @7
    cfzo
    co
    #
    wral
    #
    w3a
    #
    vf
    vp
    copab
    #
    @1
    cI
    cdm
    #
    cword
    #
    wcel
    #
    @8
    cV
    @10
    wf
    #
    @15
    @16
    cI
    cfv
    #
    @18
    wceq
    #
    @20
    @31
    wss
    #
    wif
    #
    vk
    @23
    wral
    #
    w3a
    #
    vf
    vp
    copab
    #
    cvv
    cwlks
    cvv
    cwlks
    vg
    cvv
    @26
    cmpt
    wceq
    @0
    vf
    vg
    vk
    vp
    df-wlks
    a1i
    @2
    cG
    wceq
    #
    @26
    @37
    wceq
    @0
    @38
    @25
    @36
    vf
    vp
    @38
    @6
    @29
    @11
    @30
    @24
    @35
    @38
    @5
    @28
    @1
    @38
    @4
    @27
    wceq
    @5
    @28
    wceq
    @38
    @3
    cI
    @38
    @3
    cG
    ciedg
    cfv
    #
    cI
    @2
    cG
    ciedg
    fveq2
    wksfval.i
    syl6eqr
    #
    dmeqd
    @4
    @27
    wrdeq
    syl
    eleq2d
    @38
    @9
    cV
    @10
    @8
    @38
    @9
    cG
    cvtx
    cfv
    #
    cV
    @2
    cG
    cvtx
    fveq2
    wksfval.v
    syl6eqr
    feq3d
    @38
    @22
    @34
    vk
    @23
    @38
    @15
    @19
    @21
    @15
    @32
    @33
    @38
    @15
    biidd
    @38
    @17
    @31
    @18
    @38
    @16
    @3
    cI
    @40
    fveq1d
    #
    eqeq1d
    @38
    @17
    @31
    @20
    @42
    sseq2d
    ifpbi123d
    ralbidv
    3anbi123d
    opabbidv
    adantl
    cG
    cW
    elex
    @0
    @37
    @29
    @30
    @35
    wa
    #
    wa
    #
    vf
    vp
    copab
    cvv
    @36
    @44
    vf
    vp
    @29
    @30
    @35
    3anass
    opabbii
    @0
    @43
    vf
    vp
    @28
    @27
    cvv
    wcel
    @28
    cvv
    wcel
    @0
    cI
    cI
    @39
    cvv
    wksfval.i
    cG
    ciedg
    fvex
    eqeltri
    dmex
    @27
    cvv
    wrdexg
    mp1i
    @0
    @29
    wa
    #
    @43
    vp
    cab
    #
    @30
    vp
    cab
    #
    cvv
    @45
    @8
    cvv
    wcel
    cV
    cvv
    wcel
    #
    @47
    cvv
    wcel
    cc0
    @7
    cfz
    ovex
    @48
    @45
    cV
    @41
    cvv
    wksfval.v
    cG
    cvtx
    fvex
    eqeltri
    a1i
    @8
    cV
    cvv
    cvv
    vp
    mapex
    sylancr
    @46
    @47
    wss
    @45
    @43
    @30
    vp
    @30
    @35
    simpl
    ss2abi
    a1i
    ssexd
    opabex3d
    syl5eqel
    fvmptd
end
