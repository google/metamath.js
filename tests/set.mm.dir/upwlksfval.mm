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
include "cpr.mm"
include "wceq.mm"
include "cfzo.mm"
include "wral.mm"
include "w3a.mm"
include "copab.mm"
include "cvv.mm"
include "cupwlks.mm"
include "cmpt.mm"
include "df-upwlks.mm"
include "a1i.mm"
include "fveq2.mm"
include "syl6eqr.mm"
include "dmeqd.mm"
include "wrdeq.mm"
include "syl.mm"
include "eleq2d.mm"
include "feq3d.mm"
include "fveq1d.mm"
include "eqeq1d.mm"
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
include "wss.mm"
include "simpl.mm"
include "ss2abi.mm"
include "ssexd.mm"
include "opabex3d.mm"
include "syl5eqel.mm"
include "fvmptd.mm"

theorem upwlksfval
  let vf: setvar f
  let vk: setvar k
  let cG: class G
  let cI: class I
  let cV: class V
  let cW: class W
  let vp: setvar p
  let vg: setvar g
  let vx: setvar x
  assume upwlksfval.v: |- V = ( Vtx ` G )
  assume upwlksfval.i: |- I = ( iEdg ` G )

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
  disjoint k x
  assert |- ( G e. W -> ( UPWalks ` G ) = { <. f , p >. | ( f e. Word dom I /\ p : ( 0 ... ( # ` f ) ) --> V /\ A. k e. ( 0 ..^ ( # ` f ) ) ( I ` ( f ` k ) ) = { ( p ` k ) , ( p ` ( k + 1 ) ) } ) } )

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
    @1
    cfv
    #
    @3
    cfv
    #
    @12
    @10
    cfv
    @12
    c1
    caddc
    co
    @10
    cfv
    cpr
    #
    wceq
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
    @13
    cI
    cfv
    #
    @15
    wceq
    #
    vk
    @17
    wral
    #
    w3a
    #
    vf
    vp
    copab
    #
    cvv
    cupwlks
    cvv
    cupwlks
    vg
    cvv
    @20
    cmpt
    wceq
    @0
    vf
    vg
    vk
    vp
    df-upwlks
    a1i
    @2
    cG
    wceq
    #
    @20
    @29
    wceq
    @0
    @30
    @19
    @28
    vf
    vp
    @30
    @6
    @23
    @11
    @24
    @18
    @27
    @30
    @5
    @22
    @1
    @30
    @4
    @21
    wceq
    @5
    @22
    wceq
    @30
    @3
    cI
    @30
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
    upwlksfval.i
    syl6eqr
    #
    dmeqd
    @4
    @21
    wrdeq
    syl
    eleq2d
    @30
    @9
    cV
    @10
    @8
    @30
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
    upwlksfval.v
    syl6eqr
    feq3d
    @30
    @16
    @26
    vk
    @17
    @30
    @14
    @25
    @15
    @30
    @13
    @3
    cI
    @32
    fveq1d
    eqeq1d
    ralbidv
    3anbi123d
    opabbidv
    adantl
    cG
    cW
    elex
    @0
    @29
    @23
    @24
    @27
    wa
    #
    wa
    #
    vf
    vp
    copab
    cvv
    @28
    @35
    vf
    vp
    @23
    @24
    @27
    3anass
    opabbii
    @0
    @34
    vf
    vp
    @22
    @21
    cvv
    wcel
    @22
    cvv
    wcel
    @0
    cI
    cI
    @31
    cvv
    upwlksfval.i
    cG
    ciedg
    fvex
    eqeltri
    dmex
    @21
    cvv
    wrdexg
    mp1i
    @0
    @23
    wa
    #
    @34
    vp
    cab
    #
    @24
    vp
    cab
    #
    cvv
    @36
    @8
    cvv
    wcel
    cV
    cvv
    wcel
    #
    @38
    cvv
    wcel
    cc0
    @7
    cfz
    ovex
    @39
    @36
    cV
    @33
    cvv
    upwlksfval.v
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
    @37
    @38
    wss
    @36
    @34
    @24
    vp
    @24
    @27
    simpl
    ss2abi
    a1i
    ssexd
    opabex3d
    syl5eqel
    fvmptd
end
