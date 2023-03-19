include "con0.mm"
include "wcel.mm"
include "ccnf.mm"
include "co.mm"
include "cv.mm"
include "c0.mm"
include "csupp.mm"
include "cep.mm"
include "coi.mm"
include "cdm.mm"
include "cvv.mm"
include "cfv.mm"
include "coe.mm"
include "comu.mm"
include "coa.mm"
include "cmpt2.mm"
include "cseqom.mm"
include "csb.mm"
include "cmpt.mm"
include "wceq.mm"
include "cfsupp.mm"
include "wbr.mm"
include "cmap.mm"
include "crab.mm"
include "wa.mm"
include "oveq12.mm"
include "rabeqdv.mm"
include "syl6eqr.mm"
include "w3a.mm"
include "simp1l.mm"
include "oveq1d.mm"
include "mpt2eq3dva.mm"
include "eqid.mm"
include "seqomeq12.mm"
include "sylancl.mm"
include "fveq1d.mm"
include "csbeq2dv.mm"
include "mpteq12dv.mm"
include "df-cnf.mm"
include "ovex.mm"
include "rabex2.mm"
include "mptex.mm"
include "ovmpt2a.mm"
include "syl2anc.mm"

theorem cantnffval
  let wph: wff ph
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cS: class S
  let vf: setvar f
  let vg: setvar g
  let vh: setvar h
  let vk: setvar k
  let vx: setvar x
  let vy: setvar y
  assume cantnffval.s: |- S = { g e. ( A ^m B ) | g finSupp (/) }
  assume cantnffval.a: |- ( ph -> A e. On )
  assume cantnffval.b: |- ( ph -> B e. On )

  disjoint f g
  disjoint f h
  disjoint f k
  disjoint f z
  disjoint A f
  disjoint g h
  disjoint g k
  disjoint g z
  disjoint A g
  disjoint h k
  disjoint h z
  disjoint A h
  disjoint k z
  disjoint A k
  disjoint A z
  disjoint B f
  disjoint B g
  disjoint B h
  disjoint B k
  disjoint B z
  disjoint S f
  disjoint f x
  disjoint f y
  disjoint g x
  disjoint g y
  disjoint h x
  disjoint h y
  disjoint k x
  disjoint k y
  disjoint x y
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint B x
  disjoint B y
  disjoint S x
  disjoint S y
  assert |- ( ph -> ( A CNF B ) = ( f e. S |-> [_ OrdIso ( _E , ( f supp (/) ) ) / h ]_ ( seqom ( ( k e. _V , z e. _V |-> ( ( ( A ^o ( h ` k ) ) .o ( f ` ( h ` k ) ) ) +o z ) ) , (/) ) ` dom h ) ) )

  proof
    wph
    cA
    con0
    wcel
    cB
    con0
    wcel
    cA
    cB
    ccnf
    co
    vf
    cS
    vh
    vf
    cv
    #
    c0
    csupp
    co
    cep
    coi
    #
    vh
    cv
    #
    cdm
    #
    vk
    vz
    cvv
    cvv
    cA
    vk
    cv
    #
    @2
    cfv
    #
    coe
    co
    #
    @5
    @0
    cfv
    #
    comu
    co
    #
    vz
    cv
    #
    coa
    co
    #
    cmpt2
    #
    c0
    cseqom
    #
    cfv
    #
    csb
    #
    cmpt
    #
    wceq
    cantnffval.a
    cantnffval.b
    vx
    vy
    cA
    cB
    con0
    con0
    vf
    vg
    cv
    c0
    cfsupp
    wbr
    #
    vg
    vx
    cv
    #
    vy
    cv
    #
    cmap
    co
    #
    crab
    #
    vh
    @1
    @3
    vk
    vz
    cvv
    cvv
    @17
    @5
    coe
    co
    #
    @7
    comu
    co
    #
    @9
    coa
    co
    #
    cmpt2
    #
    c0
    cseqom
    #
    cfv
    #
    csb
    #
    cmpt
    @15
    ccnf
    @17
    cA
    wceq
    #
    @18
    cB
    wceq
    #
    wa
    #
    vf
    @20
    @27
    cS
    @14
    @30
    @20
    @16
    vg
    cA
    cB
    cmap
    co
    #
    crab
    cS
    @30
    @16
    vg
    @19
    @31
    @17
    cA
    @18
    cB
    cmap
    oveq12
    rabeqdv
    cantnffval.s
    syl6eqr
    @30
    vh
    @1
    @26
    @13
    @30
    @3
    @25
    @12
    @30
    @24
    @11
    wceq
    c0
    c0
    wceq
    @25
    @12
    wceq
    @30
    vk
    vz
    cvv
    cvv
    @23
    @10
    @30
    @4
    cvv
    wcel
    #
    @9
    cvv
    wcel
    #
    w3a
    #
    @22
    @8
    @9
    coa
    @34
    @21
    @6
    @7
    comu
    @34
    @17
    cA
    @5
    coe
    @28
    @29
    @32
    @33
    simp1l
    oveq1d
    oveq1d
    oveq1d
    mpt2eq3dva
    c0
    eqid
    @24
    @11
    c0
    c0
    seqomeq12
    sylancl
    fveq1d
    csbeq2dv
    mpteq12dv
    vx
    vy
    vz
    vf
    vg
    vh
    vk
    df-cnf
    vf
    cS
    @14
    @16
    vg
    @31
    cS
    cantnffval.s
    cA
    cB
    cmap
    ovex
    rabex2
    mptex
    ovmpt2a
    syl2anc
end
