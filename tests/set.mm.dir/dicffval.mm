include "wcel.mm"
include "cvv.mm"
include "cdic.mm"
include "cfv.mm"
include "cv.mm"
include "wbr.mm"
include "wn.mm"
include "crab.mm"
include "coc.mm"
include "wceq.mm"
include "cltrn.mm"
include "crio.mm"
include "ctendo.mm"
include "wa.mm"
include "copab.mm"
include "cmpt.mm"
include "elex.mm"
include "clh.mm"
include "cple.mm"
include "catm.mm"
include "fveq2.mm"
include "syl6eqr.mm"
include "breqd.mm"
include "notbid.mm"
include "rabeqbidv.mm"
include "fveq1d.mm"
include "fveq2d.mm"
include "eqeq1d.mm"
include "riotaeqbidv.mm"
include "eqeq2d.mm"
include "eleq2d.mm"
include "anbi12d.mm"
include "opabbidv.mm"
include "mpteq12dv.mm"
include "df-dic.mm"
include "fvex.mm"
include "eqeltri.mm"
include "mptex.mm"
include "fvmpt.mm"
include "syl.mm"

theorem dicffval
  let vw: setvar w
  let cA: class A
  let vf: setvar f
  let vg: setvar g
  let cH: class H
  let cK: class K
  let c.le: class .<_
  let cV: class V
  let vs: setvar s
  let vr: setvar r
  let vq: setvar q
  let vk: setvar k
  assume dicval.l: |- .<_ = ( le ` K )
  assume dicval.a: |- A = ( Atoms ` K )
  assume dicval.h: |- H = ( LHyp ` K )

  disjoint A r
  disjoint H w
  disjoint f g
  disjoint f q
  disjoint f r
  disjoint f s
  disjoint f w
  disjoint K f
  disjoint g q
  disjoint g r
  disjoint g s
  disjoint g w
  disjoint K g
  disjoint q r
  disjoint q s
  disjoint q w
  disjoint K q
  disjoint r s
  disjoint r w
  disjoint K r
  disjoint s w
  disjoint K s
  disjoint K w
  disjoint .<_ k
  disjoint k r
  disjoint A k
  disjoint k w
  disjoint H k
  disjoint f k
  disjoint g k
  disjoint k q
  disjoint k s
  disjoint K k
  assert |- ( K e. V -> ( DIsoC ` K ) = ( w e. H |-> ( q e. { r e. A | -. r .<_ w } |-> { <. f , s >. | ( f = ( s ` ( iota_ g e. ( ( LTrn ` K ) ` w ) ( g ` ( ( oc ` K ) ` w ) ) = q ) ) /\ s e. ( ( TEndo ` K ) ` w ) ) } ) ) )

  proof
    cK
    cV
    wcel
    cK
    cvv
    wcel
    cK
    cdic
    cfv
    vw
    cH
    vq
    vr
    cv
    #
    vw
    cv
    #
    c.le
    wbr
    #
    wn
    #
    vr
    cA
    crab
    #
    vf
    cv
    #
    @1
    cK
    coc
    cfv
    #
    cfv
    #
    vg
    cv
    #
    cfv
    #
    vq
    cv
    #
    wceq
    #
    vg
    @1
    cK
    cltrn
    cfv
    #
    cfv
    #
    crio
    #
    vs
    cv
    #
    cfv
    #
    wceq
    #
    @15
    @1
    cK
    ctendo
    cfv
    #
    cfv
    #
    wcel
    #
    wa
    #
    vf
    vs
    copab
    #
    cmpt
    #
    cmpt
    #
    wceq
    cK
    cV
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
    vq
    @0
    @1
    @25
    cple
    cfv
    #
    wbr
    #
    wn
    #
    vr
    @25
    catm
    cfv
    #
    crab
    #
    @5
    @1
    @25
    coc
    cfv
    #
    cfv
    #
    @8
    cfv
    #
    @10
    wceq
    #
    vg
    @1
    @25
    cltrn
    cfv
    #
    cfv
    #
    crio
    #
    @15
    cfv
    #
    wceq
    #
    @15
    @1
    @25
    ctendo
    cfv
    #
    cfv
    #
    wcel
    #
    wa
    #
    vf
    vs
    copab
    #
    cmpt
    #
    cmpt
    @24
    cvv
    cdic
    @25
    cK
    wceq
    #
    vw
    @26
    @46
    cH
    @23
    @47
    @26
    cK
    clh
    cfv
    #
    cH
    @25
    cK
    clh
    fveq2
    dicval.h
    syl6eqr
    @47
    vq
    @31
    @45
    @4
    @22
    @47
    @29
    @3
    vr
    @30
    cA
    @47
    @30
    cK
    catm
    cfv
    cA
    @25
    cK
    catm
    fveq2
    dicval.a
    syl6eqr
    @47
    @28
    @2
    @47
    @27
    c.le
    @0
    @1
    @47
    @27
    cK
    cple
    cfv
    c.le
    @25
    cK
    cple
    fveq2
    dicval.l
    syl6eqr
    breqd
    notbid
    rabeqbidv
    @47
    @44
    @21
    vf
    vs
    @47
    @40
    @17
    @43
    @20
    @47
    @39
    @16
    @5
    @47
    @38
    @14
    @15
    @47
    @35
    @11
    vg
    @37
    @13
    @47
    @1
    @36
    @12
    @25
    cK
    cltrn
    fveq2
    fveq1d
    @47
    @34
    @9
    @10
    @47
    @33
    @7
    @8
    @47
    @1
    @32
    @6
    @25
    cK
    coc
    fveq2
    fveq1d
    fveq2d
    eqeq1d
    riotaeqbidv
    fveq2d
    eqeq2d
    @47
    @42
    @19
    @15
    @47
    @1
    @41
    @18
    @25
    cK
    ctendo
    fveq2
    fveq1d
    eleq2d
    anbi12d
    opabbidv
    mpteq12dv
    mpteq12dv
    vw
    vf
    vg
    vk
    vs
    vr
    vq
    df-dic
    vw
    cH
    @23
    cH
    @48
    cvv
    dicval.h
    cK
    clh
    fvex
    eqeltri
    mptex
    fvmpt
    syl
end
