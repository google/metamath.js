include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "cfv.mm"
include "cv.mm"
include "crab.mm"
include "wceq.mm"
include "crio.mm"
include "copab.mm"
include "cmpt.mm"
include "dicfval.mm"
include "adantr.mm"
include "fveq1d.mm"
include "simpr.mm"
include "breq1.mm"
include "notbid.mm"
include "elrab.mm"
include "sylibr.mm"
include "eqeq2.mm"
include "riotabidv.mm"
include "fveq2d.mm"
include "eqeq2d.mm"
include "anbi1d.mm"
include "opabbidv.mm"
include "eqid.mm"
include "cuni.mm"
include "crn.mm"
include "cpw.mm"
include "cxp.mm"
include "ctendo.mm"
include "cvv.mm"
include "fvex.mm"
include "eqeltri.mm"
include "uniex.mm"
include "rnex.mm"
include "pwex.mm"
include "xpex.mm"
include "simpl.mm"
include "wss.mm"
include "fvssunirn.mm"
include "elssuni.mm"
include "adantl.mm"
include "rnss.mm"
include "uniss.mm"
include "3syl.mm"
include "syl5ss.mm"
include "elpw2.mm"
include "eqeltrd.mm"
include "jca.mm"
include "ssopab2i.mm"
include "df-xp.mm"
include "sseqtr4i.mm"
include "ssexi.mm"
include "fvmpt.mm"
include "syl.mm"
include "eqtrd.mm"

theorem dicval
  let cA: class A
  let cP: class P
  let cQ: class Q
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
  let vk: setvar k
  let vr: setvar r
  let vw: setvar w
  let vq: setvar q
  assume dicval.l: |- .<_ = ( le ` K )
  assume dicval.a: |- A = ( Atoms ` K )
  assume dicval.h: |- H = ( LHyp ` K )
  assume dicval.p: |- P = ( ( oc ` K ) ` W )
  assume dicval.t: |- T = ( ( LTrn ` K ) ` W )
  assume dicval.e: |- E = ( ( TEndo ` K ) ` W )
  assume dicval.i: |- I = ( ( DIsoC ` K ) ` W )

  disjoint f g
  disjoint f s
  disjoint K f
  disjoint g s
  disjoint K g
  disjoint K s
  disjoint T g
  disjoint W f
  disjoint W g
  disjoint W s
  disjoint E f
  disjoint E s
  disjoint P f
  disjoint Q f
  disjoint Q g
  disjoint Q s
  disjoint T f
  disjoint .<_ k
  disjoint k r
  disjoint A k
  disjoint A r
  disjoint k w
  disjoint H k
  disjoint H w
  disjoint f k
  disjoint f q
  disjoint f r
  disjoint f w
  disjoint g k
  disjoint g q
  disjoint g r
  disjoint g w
  disjoint k q
  disjoint k s
  disjoint K k
  disjoint q r
  disjoint q s
  disjoint q w
  disjoint K q
  disjoint r s
  disjoint r w
  disjoint K r
  disjoint s w
  disjoint K w
  disjoint .<_ q
  disjoint .<_ w
  disjoint A q
  disjoint A w
  disjoint E w
  disjoint P w
  disjoint T w
  disjoint W q
  disjoint W r
  disjoint W w
  disjoint .<_ r
  disjoint E q
  disjoint P q
  disjoint Q q
  disjoint Q r
  disjoint T q
  assert |- ( ( ( K e. V /\ W e. H ) /\ ( Q e. A /\ -. Q .<_ W ) ) -> ( I ` Q ) = { <. f , s >. | ( f = ( s ` ( iota_ g e. T ( g ` P ) = Q ) ) /\ s e. E ) } )

  proof
    cK
    cV
    wcel
    cW
    cH
    wcel
    wa
    #
    cQ
    cA
    wcel
    cQ
    cW
    c.le
    wbr
    #
    wn
    #
    wa
    #
    wa
    #
    cQ
    cI
    cfv
    cQ
    vq
    vr
    cv
    #
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
    vf
    cv
    #
    cP
    vg
    cv
    cfv
    #
    vq
    cv
    #
    wceq
    #
    vg
    cT
    crio
    #
    vs
    cv
    #
    cfv
    #
    wceq
    #
    @14
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
    cfv
    #
    @9
    @10
    cQ
    wceq
    #
    vg
    cT
    crio
    #
    @14
    cfv
    #
    wceq
    #
    @17
    wa
    #
    vf
    vs
    copab
    #
    @4
    cQ
    cI
    @20
    @0
    cI
    @20
    wceq
    @3
    cA
    cP
    cT
    vf
    vg
    cE
    cH
    cI
    cK
    c.le
    cV
    cW
    vs
    vr
    vq
    dicval.l
    dicval.a
    dicval.h
    dicval.p
    dicval.t
    dicval.e
    dicval.i
    dicfval
    adantr
    fveq1d
    @4
    cQ
    @8
    wcel
    #
    @21
    @27
    wceq
    @4
    @3
    @28
    @0
    @3
    simpr
    @7
    @2
    vr
    cQ
    cA
    @5
    cQ
    wceq
    @6
    @1
    @5
    cQ
    cW
    c.le
    breq1
    notbid
    elrab
    sylibr
    vq
    cQ
    @19
    @27
    @8
    @20
    @11
    cQ
    wceq
    #
    @18
    @26
    vf
    vs
    @29
    @16
    @25
    @17
    @29
    @15
    @24
    @9
    @29
    @13
    @23
    @14
    @29
    @12
    @22
    vg
    cT
    @11
    cQ
    @10
    eqeq2
    riotabidv
    fveq2d
    eqeq2d
    anbi1d
    opabbidv
    @20
    eqid
    @27
    cE
    cuni
    #
    crn
    #
    cuni
    #
    cpw
    #
    cE
    cxp
    #
    @33
    cE
    @32
    @31
    @30
    cE
    cE
    cW
    cK
    ctendo
    cfv
    #
    cfv
    cvv
    dicval.e
    cW
    @35
    fvex
    eqeltri
    #
    uniex
    rnex
    uniex
    #
    pwex
    @36
    xpex
    @27
    @9
    @33
    wcel
    #
    @17
    wa
    #
    vf
    vs
    copab
    @34
    @26
    @39
    vf
    vs
    @26
    @38
    @17
    @26
    @9
    @24
    @33
    @25
    @17
    simpl
    @26
    @24
    @32
    wss
    @24
    @33
    wcel
    @26
    @24
    @14
    crn
    #
    cuni
    #
    @32
    @14
    @23
    fvssunirn
    @26
    @14
    @30
    wss
    #
    @40
    @31
    wss
    @41
    @32
    wss
    @17
    @42
    @25
    @14
    cE
    elssuni
    adantl
    @14
    @30
    rnss
    @40
    @31
    uniss
    3syl
    syl5ss
    @24
    @32
    @37
    elpw2
    sylibr
    eqeltrd
    @25
    @17
    simpr
    jca
    ssopab2i
    vf
    vs
    @33
    cE
    df-xp
    sseqtr4i
    ssexi
    fvmpt
    syl
    eqtrd
end
