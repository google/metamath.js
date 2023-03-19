include "cc.mm"
include "wf.mm"
include "wss.mm"
include "wcel.mm"
include "w3a.mm"
include "climc.mm"
include "co.mm"
include "csn.mm"
include "cun.mm"
include "cv.mm"
include "wceq.mm"
include "cfv.mm"
include "cif.mm"
include "cmpt.mm"
include "ccnp.mm"
include "cab.mm"
include "cpm.mm"
include "cdm.mm"
include "crest.mm"
include "ccnfld.mm"
include "ctopn.mm"
include "wsbc.mm"
include "cvv.mm"
include "cmpt2.mm"
include "df-limc.mm"
include "a1i.mm"
include "wa.mm"
include "fvexd.mm"
include "simplrl.mm"
include "dmeqd.mm"
include "simpll1.mm"
include "fdm.mm"
include "syl.mm"
include "eqtrd.mm"
include "simplrr.mm"
include "sneqd.mm"
include "uneq12d.mm"
include "eqeq2d.mm"
include "fveq1d.mm"
include "ifbieq2d.mm"
include "mpteq12dv.mm"
include "simpr.mm"
include "syl6eqr.mm"
include "oveq12d.mm"
include "fveq12d.mm"
include "eleq12d.mm"
include "sbcied.mm"
include "abbidv.mm"
include "cnex.mm"
include "elpm2r.mm"
include "mpanl12.mm"
include "3adant3.mm"
include "simp3.mm"
include "eqid.mm"
include "limcvallem.mm"
include "abssdv.mm"
include "ssex.mm"
include "ovmpt2d.mm"
include "eqsstrd.mm"
include "jca.mm"

theorem limcfval
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cF: class F
  let cJ: class J
  let cK: class K
  let vf: setvar f
  let vj: setvar j
  let vx: setvar x
  let cC: class C
  let cG: class G
  assume limcval.j: |- J = ( K |`t ( A u. { B } ) )
  assume limcval.k: |- K = ( TopOpen ` CCfld )

  disjoint y z
  disjoint A y
  disjoint A z
  disjoint B y
  disjoint B z
  disjoint F y
  disjoint F z
  disjoint K y
  disjoint K z
  disjoint J y
  disjoint f j
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint A f
  disjoint j x
  disjoint j y
  disjoint j z
  disjoint A j
  disjoint x y
  disjoint x z
  disjoint A x
  disjoint B f
  disjoint B j
  disjoint B x
  disjoint F f
  disjoint F j
  disjoint F x
  disjoint K f
  disjoint K j
  disjoint K x
  disjoint C y
  disjoint C z
  disjoint G y
  disjoint J f
  disjoint J j
  disjoint J x
  assert |- ( ( F : A --> CC /\ A C_ CC /\ B e. CC ) -> ( ( F limCC B ) = { y | ( z e. ( A u. { B } ) |-> if ( z = B , y , ( F ` z ) ) ) e. ( ( J CnP K ) ` B ) } /\ ( F limCC B ) C_ CC ) )

  proof
    cA
    cc
    cF
    wf
    #
    cA
    cc
    wss
    #
    cB
    cc
    wcel
    #
    w3a
    #
    cF
    cB
    climc
    co
    #
    vz
    cA
    cB
    csn
    #
    cun
    #
    vz
    cv
    #
    cB
    wceq
    #
    vy
    cv
    #
    @7
    cF
    cfv
    #
    cif
    #
    cmpt
    #
    cB
    cJ
    cK
    ccnp
    co
    #
    cfv
    #
    wcel
    #
    vy
    cab
    #
    wceq
    @4
    cc
    wss
    @3
    vf
    vx
    cF
    cB
    cc
    cc
    cpm
    co
    #
    cc
    vz
    vf
    cv
    #
    cdm
    #
    vx
    cv
    #
    csn
    #
    cun
    #
    @7
    @20
    wceq
    #
    @9
    @7
    @18
    cfv
    #
    cif
    #
    cmpt
    #
    @20
    vj
    cv
    #
    @22
    crest
    co
    #
    @27
    ccnp
    co
    #
    cfv
    #
    wcel
    #
    vj
    ccnfld
    ctopn
    cfv
    #
    wsbc
    #
    vy
    cab
    #
    @16
    climc
    cvv
    climc
    vf
    vx
    @17
    cc
    @34
    cmpt2
    wceq
    @3
    vx
    vy
    vz
    vf
    vj
    df-limc
    a1i
    @3
    @18
    cF
    wceq
    #
    @20
    cB
    wceq
    #
    wa
    #
    wa
    #
    @33
    @15
    vy
    @38
    @31
    @15
    vj
    @32
    cvv
    @38
    ccnfld
    ctopn
    fvexd
    @38
    @27
    @32
    wceq
    #
    wa
    #
    @26
    @12
    @30
    @14
    @40
    vz
    @22
    @25
    @6
    @11
    @40
    @19
    cA
    @21
    @5
    @40
    @19
    cF
    cdm
    #
    cA
    @40
    @18
    cF
    @3
    @35
    @36
    @39
    simplrl
    #
    dmeqd
    @40
    @0
    @41
    cA
    wceq
    @0
    @1
    @2
    @37
    @39
    simpll1
    cA
    cc
    cF
    fdm
    syl
    eqtrd
    @40
    @20
    cB
    @3
    @35
    @36
    @39
    simplrr
    #
    sneqd
    uneq12d
    #
    @40
    @23
    @8
    @24
    @10
    @9
    @40
    @20
    cB
    @7
    @43
    eqeq2d
    @40
    @7
    @18
    cF
    @42
    fveq1d
    ifbieq2d
    mpteq12dv
    @40
    @20
    cB
    @29
    @13
    @40
    @28
    cJ
    @27
    cK
    ccnp
    @40
    @28
    cK
    @6
    crest
    co
    cJ
    @40
    @27
    cK
    @22
    @6
    crest
    @40
    @27
    @32
    cK
    @38
    @39
    simpr
    limcval.k
    syl6eqr
    #
    @44
    oveq12d
    limcval.j
    syl6eqr
    @45
    oveq12d
    @43
    fveq12d
    eleq12d
    sbcied
    abbidv
    @0
    @1
    cF
    @17
    wcel
    #
    @2
    cc
    cvv
    wcel
    #
    @47
    @0
    @1
    wa
    @46
    cnex
    cnex
    cc
    cc
    cA
    cF
    cvv
    cvv
    elpm2r
    mpanl12
    3adant3
    @0
    @1
    @2
    simp3
    @3
    @16
    cc
    wss
    @16
    cvv
    wcel
    @3
    @15
    vy
    cc
    vz
    cA
    cB
    @9
    cF
    @12
    cJ
    cK
    limcval.j
    limcval.k
    @12
    eqid
    limcvallem
    abssdv
    #
    @16
    cc
    cnex
    ssex
    syl
    ovmpt2d
    #
    @3
    @4
    @16
    cc
    @49
    @48
    eqsstrd
    jca
end
