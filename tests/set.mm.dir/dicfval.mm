include "wcel.mm"
include "cv.mm"
include "wbr.mm"
include "wn.mm"
include "crab.mm"
include "coc.mm"
include "cfv.mm"
include "wceq.mm"
include "cltrn.mm"
include "crio.mm"
include "ctendo.mm"
include "wa.mm"
include "copab.mm"
include "cmpt.mm"
include "cdic.mm"
include "dicffval.mm"
include "fveq1d.mm"
include "syl5eq.mm"
include "breq2.mm"
include "notbid.mm"
include "rabbidv.mm"
include "fveq2.mm"
include "syl6eqr.mm"
include "fveq2d.mm"
include "eqeq1d.mm"
include "riotaeqbidv.mm"
include "eqeq2d.mm"
include "eleq2d.mm"
include "anbi12d.mm"
include "opabbidv.mm"
include "mpteq12dv.mm"
include "eqid.mm"
include "catm.mm"
include "cvv.mm"
include "fvex.mm"
include "eqeltri.mm"
include "mptrabex.mm"
include "fvmpt.mm"
include "sylan9eq.mm"

theorem dicfval
  let cA: class A
  let cP: class P
  let cT: class T
  let vf: setvar f
  let vg: setvar g
  let cE: class E
  let cH: class H
  let cI: class I
  let cK: class K
  let c.le: class .<_
  let cV: class V
  let cW: class W
  let vs: setvar s
  let vr: setvar r
  let vq: setvar q
  let vk: setvar k
  let vw: setvar w
  assume dicval.l: |- .<_ = ( le ` K )
  assume dicval.a: |- A = ( Atoms ` K )
  assume dicval.h: |- H = ( LHyp ` K )
  assume dicval.p: |- P = ( ( oc ` K ) ` W )
  assume dicval.t: |- T = ( ( LTrn ` K ) ` W )
  assume dicval.e: |- E = ( ( TEndo ` K ) ` W )
  assume dicval.i: |- I = ( ( DIsoC ` K ) ` W )

  disjoint A r
  disjoint f g
  disjoint f q
  disjoint f r
  disjoint f s
  disjoint K f
  disjoint g q
  disjoint g r
  disjoint g s
  disjoint K g
  disjoint q r
  disjoint q s
  disjoint K q
  disjoint r s
  disjoint K r
  disjoint K s
  disjoint .<_ q
  disjoint A q
  disjoint T g
  disjoint W f
  disjoint W g
  disjoint W q
  disjoint W r
  disjoint W s
  disjoint .<_ k
  disjoint k r
  disjoint A k
  disjoint k w
  disjoint H k
  disjoint H w
  disjoint f k
  disjoint f w
  disjoint g k
  disjoint g w
  disjoint k q
  disjoint k s
  disjoint K k
  disjoint q w
  disjoint r w
  disjoint s w
  disjoint K w
  disjoint .<_ w
  disjoint A w
  disjoint E w
  disjoint P w
  disjoint T w
  disjoint W w
  assert |- ( ( K e. V /\ W e. H ) -> I = ( q e. { r e. A | -. r .<_ W } |-> { <. f , s >. | ( f = ( s ` ( iota_ g e. T ( g ` P ) = q ) ) /\ s e. E ) } ) )

  proof
    cK
    cV
    wcel
    #
    cW
    cH
    wcel
    cI
    cW
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
    @2
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
    @2
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
    @16
    @2
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
    cfv
    #
    vq
    @1
    cW
    c.le
    wbr
    #
    wn
    #
    vr
    cA
    crab
    #
    @6
    cP
    @9
    cfv
    #
    @11
    wceq
    #
    vg
    cT
    crio
    #
    @16
    cfv
    #
    wceq
    #
    @16
    cE
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
    @0
    cI
    cW
    cK
    cdic
    cfv
    #
    cfv
    @26
    dicval.i
    @0
    cW
    @39
    @25
    vw
    cA
    vf
    vg
    cH
    cK
    c.le
    cV
    vs
    vr
    vq
    dicval.l
    dicval.a
    dicval.h
    dicffval
    fveq1d
    syl5eq
    vw
    cW
    @24
    @38
    cH
    @25
    @2
    cW
    wceq
    #
    vq
    @5
    @23
    @29
    @37
    @40
    @4
    @28
    vr
    cA
    @40
    @3
    @27
    @2
    cW
    @1
    c.le
    breq2
    notbid
    rabbidv
    @40
    @22
    @36
    vf
    vs
    @40
    @18
    @34
    @21
    @35
    @40
    @17
    @33
    @6
    @40
    @15
    @32
    @16
    @40
    @12
    @31
    vg
    @14
    cT
    @40
    @14
    cW
    @13
    cfv
    cT
    @2
    cW
    @13
    fveq2
    dicval.t
    syl6eqr
    @40
    @10
    @30
    @11
    @40
    @8
    cP
    @9
    @40
    @8
    cW
    @7
    cfv
    cP
    @2
    cW
    @7
    fveq2
    dicval.p
    syl6eqr
    fveq2d
    eqeq1d
    riotaeqbidv
    fveq2d
    eqeq2d
    @40
    @20
    cE
    @16
    @40
    @20
    cW
    @19
    cfv
    cE
    @2
    cW
    @19
    fveq2
    dicval.e
    syl6eqr
    eleq2d
    anbi12d
    opabbidv
    mpteq12dv
    @25
    eqid
    @28
    vq
    vr
    cA
    @37
    cA
    cK
    catm
    cfv
    cvv
    dicval.a
    cK
    catm
    fvex
    eqeltri
    mptrabex
    fvmpt
    sylan9eq
end
