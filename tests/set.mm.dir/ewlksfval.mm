include "wcel.mm"
include "cxnn0.mm"
include "wa.mm"
include "cewlks.mm"
include "co.mm"
include "cv.mm"
include "ciedg.mm"
include "cfv.mm"
include "cdm.mm"
include "cword.mm"
include "c1.mm"
include "cmin.mm"
include "cin.mm"
include "chash.mm"
include "cle.mm"
include "wbr.mm"
include "cfzo.mm"
include "wral.mm"
include "cab.mm"
include "cvv.mm"
include "wsbc.mm"
include "cmpt2.mm"
include "wceq.mm"
include "df-ewlks.mm"
include "a1i.mm"
include "fvexd.mm"
include "simpr.mm"
include "fveq2.mm"
include "adantr.mm"
include "eqtrd.mm"
include "dmeqd.mm"
include "wrdeq.mm"
include "syl.mm"
include "eleq2d.mm"
include "fveq1d.mm"
include "ineq12d.mm"
include "fveq2d.mm"
include "breq12d.mm"
include "ralbidv.mm"
include "anbi12d.mm"
include "sbcied.mm"
include "abbidv.mm"
include "adantl.mm"
include "elex.mm"
include "crab.mm"
include "df-rab.mm"
include "fvex.mm"
include "dmex.mm"
include "wrdexi.mm"
include "rabex.mm"
include "syl5eqelr.mm"
include "ovmpt2d.mm"
include "eqcomi.mm"
include "breq2d.mm"

theorem ewlksfval
  let cS: class S
  let vf: setvar f
  let vk: setvar k
  let cG: class G
  let cI: class I
  let cW: class W
  let vg: setvar g
  let vi: setvar i
  let vs: setvar s
  assume ewlksfval.i: |- I = ( iEdg ` G )

  disjoint G f
  disjoint G k
  disjoint f k
  disjoint S f
  disjoint S k
  disjoint W f
  disjoint W k
  disjoint G g
  disjoint G i
  disjoint G s
  disjoint f g
  disjoint f i
  disjoint f s
  disjoint g i
  disjoint g k
  disjoint g s
  disjoint i k
  disjoint i s
  disjoint k s
  disjoint S g
  disjoint S i
  disjoint S s
  disjoint W g
  disjoint W s
  assert |- ( ( G e. W /\ S e. NN0* ) -> ( G EdgWalks S ) = { f | ( f e. Word dom I /\ A. k e. ( 1 ..^ ( # ` f ) ) S <_ ( # ` ( ( I ` ( f ` ( k - 1 ) ) ) i^i ( I ` ( f ` k ) ) ) ) ) } )

  proof
    cG
    cW
    wcel
    #
    cS
    cxnn0
    wcel
    #
    wa
    #
    cG
    cS
    cewlks
    co
    vf
    cv
    #
    cG
    ciedg
    cfv
    #
    cdm
    #
    cword
    #
    wcel
    #
    cS
    vk
    cv
    #
    c1
    cmin
    co
    @3
    cfv
    #
    @4
    cfv
    #
    @8
    @3
    cfv
    #
    @4
    cfv
    #
    cin
    #
    chash
    cfv
    #
    cle
    wbr
    #
    vk
    c1
    @3
    chash
    cfv
    cfzo
    co
    #
    wral
    #
    wa
    #
    vf
    cab
    #
    @3
    cI
    cdm
    #
    cword
    #
    wcel
    #
    cS
    @9
    cI
    cfv
    #
    @11
    cI
    cfv
    #
    cin
    #
    chash
    cfv
    #
    cle
    wbr
    #
    vk
    @16
    wral
    #
    wa
    #
    vf
    cab
    @2
    vg
    vs
    cG
    cS
    cvv
    cxnn0
    @3
    vi
    cv
    #
    cdm
    #
    cword
    #
    wcel
    #
    vs
    cv
    #
    @9
    @30
    cfv
    #
    @11
    @30
    cfv
    #
    cin
    #
    chash
    cfv
    #
    cle
    wbr
    #
    vk
    @16
    wral
    #
    wa
    #
    vi
    vg
    cv
    #
    ciedg
    cfv
    #
    wsbc
    #
    vf
    cab
    #
    @19
    cewlks
    cvv
    cewlks
    vg
    vs
    cvv
    cxnn0
    @45
    cmpt2
    wceq
    @2
    vf
    vg
    vi
    vk
    vs
    df-ewlks
    a1i
    @42
    cG
    wceq
    #
    @34
    cS
    wceq
    #
    wa
    #
    @45
    @19
    wceq
    @2
    @48
    @44
    @18
    vf
    @48
    @41
    @18
    vi
    @43
    cvv
    @48
    @42
    ciedg
    fvexd
    @48
    @30
    @43
    wceq
    #
    wa
    #
    @33
    @7
    @40
    @17
    @50
    @32
    @6
    @3
    @50
    @31
    @5
    wceq
    @32
    @6
    wceq
    @50
    @30
    @4
    @50
    @30
    @43
    @4
    @48
    @49
    simpr
    @48
    @43
    @4
    wceq
    #
    @49
    @46
    @51
    @47
    @42
    cG
    ciedg
    fveq2
    adantr
    adantr
    eqtrd
    #
    dmeqd
    @31
    @5
    wrdeq
    syl
    eleq2d
    @50
    @39
    @15
    vk
    @16
    @50
    @34
    cS
    @38
    @14
    cle
    @48
    @47
    @49
    @46
    @47
    simpr
    adantr
    @50
    @37
    @13
    chash
    @50
    @35
    @10
    @36
    @12
    @50
    @9
    @30
    @4
    @52
    fveq1d
    @50
    @11
    @30
    @4
    @52
    fveq1d
    ineq12d
    fveq2d
    breq12d
    ralbidv
    anbi12d
    sbcied
    abbidv
    adantl
    @0
    cG
    cvv
    wcel
    @1
    cG
    cW
    elex
    adantr
    @0
    @1
    simpr
    @2
    @19
    @17
    vf
    @6
    crab
    #
    cvv
    @17
    vf
    @6
    df-rab
    @53
    cvv
    wcel
    @2
    @17
    vf
    @6
    @5
    @4
    cG
    ciedg
    fvex
    dmex
    wrdexi
    rabex
    a1i
    syl5eqelr
    ovmpt2d
    @2
    @18
    @29
    vf
    @2
    @7
    @22
    @17
    @28
    @2
    @6
    @21
    @3
    @2
    @5
    @20
    wceq
    @6
    @21
    wceq
    @2
    @4
    cI
    @4
    cI
    wceq
    @2
    cI
    @4
    ewlksfval.i
    eqcomi
    a1i
    #
    dmeqd
    @5
    @20
    wrdeq
    syl
    eleq2d
    @2
    @15
    @27
    vk
    @16
    @2
    @14
    @26
    cS
    cle
    @2
    @13
    @25
    chash
    @2
    @10
    @23
    @12
    @24
    @2
    @9
    @4
    cI
    @54
    fveq1d
    @2
    @11
    @4
    cI
    @54
    fveq1d
    ineq12d
    fveq2d
    breq2d
    ralbidv
    anbi12d
    abbidv
    eqtrd
end
