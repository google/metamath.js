include "wcel.mm"
include "cvv.mm"
include "cmpd.mm"
include "cfv.mm"
include "cv.mm"
include "cdvh.mm"
include "clss.mm"
include "clk.mm"
include "coch.mm"
include "wceq.mm"
include "wss.mm"
include "wa.mm"
include "clfn.mm"
include "crab.mm"
include "cmpt.mm"
include "elex.mm"
include "clh.mm"
include "fveq2.mm"
include "syl6eqr.mm"
include "fveq1d.mm"
include "fveq2d.mm"
include "fveq12d.mm"
include "eqeq12d.mm"
include "sseq1d.mm"
include "anbi12d.mm"
include "rabeqbidv.mm"
include "mpteq12dv.mm"
include "df-mapd.mm"
include "fvex.mm"
include "eqeltri.mm"
include "mptex.mm"
include "fvmpt.mm"
include "syl.mm"

theorem mapdffval
  let vw: setvar w
  let vf: setvar f
  let cH: class H
  let cK: class K
  let cX: class X
  let vs: setvar s
  let vk: setvar k
  assume mapdval.h: |- H = ( LHyp ` K )

  disjoint H w
  disjoint f s
  disjoint f w
  disjoint K f
  disjoint s w
  disjoint K s
  disjoint K w
  disjoint k w
  disjoint H k
  disjoint f k
  disjoint k s
  disjoint K k
  assert |- ( K e. X -> ( mapd ` K ) = ( w e. H |-> ( s e. ( LSubSp ` ( ( DVecH ` K ) ` w ) ) |-> { f e. ( LFnl ` ( ( DVecH ` K ) ` w ) ) | ( ( ( ( ocH ` K ) ` w ) ` ( ( ( ocH ` K ) ` w ) ` ( ( LKer ` ( ( DVecH ` K ) ` w ) ) ` f ) ) ) = ( ( LKer ` ( ( DVecH ` K ) ` w ) ) ` f ) /\ ( ( ( ocH ` K ) ` w ) ` ( ( LKer ` ( ( DVecH ` K ) ` w ) ) ` f ) ) C_ s ) } ) ) )

  proof
    cK
    cX
    wcel
    cK
    cvv
    wcel
    cK
    cmpd
    cfv
    vw
    cH
    vs
    vw
    cv
    #
    cK
    cdvh
    cfv
    #
    cfv
    #
    clss
    cfv
    #
    vf
    cv
    #
    @2
    clk
    cfv
    #
    cfv
    #
    @0
    cK
    coch
    cfv
    #
    cfv
    #
    cfv
    #
    @8
    cfv
    #
    @6
    wceq
    #
    @9
    vs
    cv
    #
    wss
    #
    wa
    #
    vf
    @2
    clfn
    cfv
    #
    crab
    #
    cmpt
    #
    cmpt
    #
    wceq
    cK
    cX
    elex
    vk
    cK
    vw
    vk
    cv
    #
    clh
    cfv
    #
    vs
    @0
    @19
    cdvh
    cfv
    #
    cfv
    #
    clss
    cfv
    #
    @4
    @22
    clk
    cfv
    #
    cfv
    #
    @0
    @19
    coch
    cfv
    #
    cfv
    #
    cfv
    #
    @27
    cfv
    #
    @25
    wceq
    #
    @28
    @12
    wss
    #
    wa
    #
    vf
    @22
    clfn
    cfv
    #
    crab
    #
    cmpt
    #
    cmpt
    @18
    cvv
    cmpd
    @19
    cK
    wceq
    #
    vw
    @20
    @35
    cH
    @17
    @36
    @20
    cK
    clh
    cfv
    #
    cH
    @19
    cK
    clh
    fveq2
    mapdval.h
    syl6eqr
    @36
    vs
    @23
    @34
    @3
    @16
    @36
    @22
    @2
    clss
    @36
    @0
    @21
    @1
    @19
    cK
    cdvh
    fveq2
    fveq1d
    #
    fveq2d
    @36
    @32
    @14
    vf
    @33
    @15
    @36
    @22
    @2
    clfn
    @38
    fveq2d
    @36
    @30
    @11
    @31
    @13
    @36
    @29
    @10
    @25
    @6
    @36
    @28
    @9
    @27
    @8
    @36
    @0
    @26
    @7
    @19
    cK
    coch
    fveq2
    fveq1d
    #
    @36
    @25
    @6
    @27
    @8
    @39
    @36
    @4
    @24
    @5
    @36
    @22
    @2
    clk
    @38
    fveq2d
    fveq1d
    #
    fveq12d
    #
    fveq12d
    @40
    eqeq12d
    @36
    @28
    @9
    @12
    @41
    sseq1d
    anbi12d
    rabeqbidv
    mpteq12dv
    mpteq12dv
    vw
    vf
    vk
    vs
    df-mapd
    vw
    cH
    @17
    cH
    @37
    cvv
    mapdval.h
    cK
    clh
    fvex
    eqeltri
    mptex
    fvmpt
    syl
end
