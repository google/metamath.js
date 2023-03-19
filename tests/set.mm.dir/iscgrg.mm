include "wcel.mm"
include "wbr.mm"
include "cv.mm"
include "cr.mm"
include "cpm.mm"
include "co.mm"
include "wa.mm"
include "cdm.mm"
include "wceq.mm"
include "cfv.mm"
include "wral.mm"
include "copab.mm"
include "ccgrg.mm"
include "cvv.mm"
include "elex.mm"
include "cbs.mm"
include "cds.mm"
include "fveq2.mm"
include "syl6eqr.mm"
include "oveq1d.mm"
include "eleq2d.mm"
include "anbi12d.mm"
include "oveqd.mm"
include "eqeq12d.mm"
include "2ralbidv.mm"
include "anbi2d.mm"
include "opabbidv.mm"
include "df-cgrg.mm"
include "cxp.mm"
include "df-xp.mm"
include "ovex.mm"
include "xpex.mm"
include "eqeltrri.mm"
include "simpl.mm"
include "ssopab2i.mm"
include "ssexi.mm"
include "fvmpt.mm"
include "syl.mm"
include "syl5eq.mm"
include "breqd.mm"
include "dmeq.mm"
include "eqeq1d.mm"
include "adantr.mm"
include "simpll.mm"
include "fveq1d.mm"
include "oveq12d.mm"
include "raleqbidva.mm"
include "eqeq2d.mm"
include "fveq1.mm"
include "sylan9bb.mm"
include "eqid.mm"
include "brab2a.mm"
include "syl6bb.mm"

theorem iscgrg
  let cA: class A
  let cB: class B
  let cP: class P
  let c.sm: class .~
  let vi: setvar i
  let vj: setvar j
  let cG: class G
  let c.mi: class .-
  let cV: class V
  let va: setvar a
  let vb: setvar b
  let vg: setvar g
  assume iscgrg.p: |- P = ( Base ` G )
  assume iscgrg.m: |- .- = ( dist ` G )
  assume iscgrg.e: |- .~ = ( cgrG ` G )

  disjoint i j
  disjoint G i
  disjoint G j
  disjoint A i
  disjoint A j
  disjoint B i
  disjoint B j
  disjoint a b
  disjoint a g
  disjoint a i
  disjoint a j
  disjoint G a
  disjoint b g
  disjoint b i
  disjoint b j
  disjoint G b
  disjoint g i
  disjoint g j
  disjoint G g
  disjoint .- a
  disjoint .- b
  disjoint .- g
  disjoint A a
  disjoint A b
  disjoint B a
  disjoint B b
  disjoint P a
  disjoint P b
  disjoint P g
  assert |- ( G e. V -> ( A .~ B <-> ( ( A e. ( P ^pm RR ) /\ B e. ( P ^pm RR ) ) /\ ( dom A = dom B /\ A. i e. dom A A. j e. dom A ( ( A ` i ) .- ( A ` j ) ) = ( ( B ` i ) .- ( B ` j ) ) ) ) ) )

  proof
    cG
    cV
    wcel
    #
    cA
    cB
    c.sm
    wbr
    cA
    cB
    va
    cv
    #
    cP
    cr
    cpm
    co
    #
    wcel
    #
    vb
    cv
    #
    @2
    wcel
    #
    wa
    #
    @1
    cdm
    #
    @4
    cdm
    #
    wceq
    #
    vi
    cv
    #
    @1
    cfv
    #
    vj
    cv
    #
    @1
    cfv
    #
    c.mi
    co
    #
    @10
    @4
    cfv
    #
    @12
    @4
    cfv
    #
    c.mi
    co
    #
    wceq
    #
    vj
    @7
    wral
    #
    vi
    @7
    wral
    #
    wa
    #
    wa
    #
    va
    vb
    copab
    #
    wbr
    cA
    @2
    wcel
    cB
    @2
    wcel
    wa
    cA
    cdm
    #
    cB
    cdm
    #
    wceq
    #
    @10
    cA
    cfv
    #
    @12
    cA
    cfv
    #
    c.mi
    co
    #
    @10
    cB
    cfv
    #
    @12
    cB
    cfv
    #
    c.mi
    co
    #
    wceq
    #
    vj
    @24
    wral
    vi
    @24
    wral
    #
    wa
    #
    wa
    @0
    c.sm
    @23
    cA
    cB
    @0
    c.sm
    cG
    ccgrg
    cfv
    #
    @23
    iscgrg.e
    @0
    cG
    cvv
    wcel
    @36
    @23
    wceq
    cG
    cV
    elex
    vg
    cG
    @1
    vg
    cv
    #
    cbs
    cfv
    #
    cr
    cpm
    co
    #
    wcel
    #
    @4
    @39
    wcel
    #
    wa
    #
    @9
    @11
    @13
    @37
    cds
    cfv
    #
    co
    #
    @15
    @16
    @43
    co
    #
    wceq
    #
    vj
    @7
    wral
    vi
    @7
    wral
    #
    wa
    #
    wa
    #
    va
    vb
    copab
    @23
    cvv
    ccgrg
    @37
    cG
    wceq
    #
    @49
    @22
    va
    vb
    @50
    @42
    @6
    @48
    @21
    @50
    @40
    @3
    @41
    @5
    @50
    @39
    @2
    @1
    @50
    @38
    cP
    cr
    cpm
    @50
    @38
    cG
    cbs
    cfv
    cP
    @37
    cG
    cbs
    fveq2
    iscgrg.p
    syl6eqr
    oveq1d
    #
    eleq2d
    @50
    @39
    @2
    @4
    @51
    eleq2d
    anbi12d
    @50
    @47
    @20
    @9
    @50
    @46
    @18
    vi
    vj
    @7
    @7
    @50
    @44
    @14
    @45
    @17
    @50
    @43
    c.mi
    @11
    @13
    @50
    @43
    cG
    cds
    cfv
    c.mi
    @37
    cG
    cds
    fveq2
    iscgrg.m
    syl6eqr
    #
    oveqd
    @50
    @43
    c.mi
    @15
    @16
    @52
    oveqd
    eqeq12d
    2ralbidv
    anbi2d
    anbi12d
    opabbidv
    vg
    vi
    vj
    va
    vb
    df-cgrg
    @23
    @6
    va
    vb
    copab
    #
    @2
    @2
    cxp
    @53
    cvv
    va
    vb
    @2
    @2
    df-xp
    @2
    @2
    cP
    cr
    cpm
    ovex
    #
    @54
    xpex
    eqeltrri
    @22
    @6
    va
    vb
    @6
    @21
    simpl
    ssopab2i
    ssexi
    fvmpt
    syl
    syl5eq
    breqd
    @21
    @35
    va
    vb
    cA
    cB
    @2
    @2
    @23
    @1
    cA
    wceq
    #
    @21
    @24
    @8
    wceq
    #
    @29
    @17
    wceq
    #
    vj
    @24
    wral
    #
    vi
    @24
    wral
    #
    wa
    @4
    cB
    wceq
    #
    @35
    @55
    @9
    @56
    @20
    @59
    @55
    @7
    @24
    @8
    @1
    cA
    dmeq
    #
    eqeq1d
    @55
    @19
    @58
    vi
    @7
    @24
    @61
    @55
    @10
    @7
    wcel
    #
    wa
    #
    @18
    @57
    vj
    @7
    @24
    @55
    @7
    @24
    wceq
    @62
    @61
    adantr
    @63
    @12
    @7
    wcel
    #
    wa
    #
    @14
    @29
    @17
    @65
    @11
    @27
    @13
    @28
    c.mi
    @65
    @10
    @1
    cA
    @55
    @62
    @64
    simpll
    #
    fveq1d
    @65
    @12
    @1
    cA
    @66
    fveq1d
    oveq12d
    eqeq1d
    raleqbidva
    raleqbidva
    anbi12d
    @60
    @56
    @26
    @59
    @34
    @60
    @8
    @25
    @24
    @4
    cB
    dmeq
    eqeq2d
    @60
    @57
    @33
    vi
    vj
    @24
    @24
    @60
    @17
    @32
    @29
    @60
    @15
    @30
    @16
    @31
    c.mi
    @10
    @4
    cB
    fveq1
    @12
    @4
    cB
    fveq1
    oveq12d
    eqeq2d
    2ralbidv
    anbi12d
    sylan9bb
    @23
    eqid
    brab2a
    syl6bb
end
