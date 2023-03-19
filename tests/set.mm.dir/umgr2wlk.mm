include "cumgr.mm"
include "wcel.mm"
include "cpr.mm"
include "w3a.mm"
include "cv.mm"
include "ciedg.mm"
include "cfv.mm"
include "wceq.mm"
include "cdm.mm"
include "wrex.mm"
include "cwlks.mm"
include "wbr.mm"
include "chash.mm"
include "c2.mm"
include "cc0.mm"
include "c1.mm"
include "wex.mm"
include "wi.mm"
include "cuhgr.mm"
include "wb.mm"
include "umgruhgr.mm"
include "cedg.mm"
include "eleq2i.mm"
include "eqid.mm"
include "uhgredgiedgb.mm"
include "syl5bb.mm"
include "syl.mm"
include "biimpd.mm"
include "a1d.mm"
include "3imp.mm"
include "a1dd.mm"
include "cs2.mm"
include "cvv.mm"
include "cword.mm"
include "cs3.mm"
include "wa.mm"
include "s2cli.mm"
include "s3cli.mm"
include "pm3.2i.mm"
include "simpl1.mm"
include "3simpc.mm"
include "adantr.mm"
include "simpl.mm"
include "eqcomd.mm"
include "adantl.mm"
include "simpr.mm"
include "umgr2adedgwlk.mm"
include "breq12.mm"
include "fveq2.mm"
include "eqeq1d.mm"
include "fveq1.mm"
include "eqeq2d.mm"
include "3anbi123d.mm"
include "spc2egv.mm"
include "mpsyl.mm"
include "exp32.mm"
include "com12.mm"
include "rexlimivw.mm"
include "com13.mm"
include "mp2d.mm"

theorem umgr2wlk
  let cA: class A
  let cB: class B
  let cC: class C
  let vf: setvar f
  let cE: class E
  let cG: class G
  let vp: setvar p
  let vi: setvar i
  let vj: setvar j
  assume umgr2wlk.e: |- E = ( Edg ` G )

  disjoint A f
  disjoint A p
  disjoint f p
  disjoint B f
  disjoint B p
  disjoint C f
  disjoint C p
  disjoint G f
  disjoint G p
  disjoint A i
  disjoint A j
  disjoint f i
  disjoint f j
  disjoint i j
  disjoint i p
  disjoint j p
  disjoint B i
  disjoint B j
  disjoint C i
  disjoint C j
  disjoint E i
  disjoint E j
  disjoint G i
  disjoint G j
  assert |- ( ( G e. UMGraph /\ { A , B } e. E /\ { B , C } e. E ) -> E. f E. p ( f ( Walks ` G ) p /\ ( # ` f ) = 2 /\ ( A = ( p ` 0 ) /\ B = ( p ` 1 ) /\ C = ( p ` 2 ) ) ) )

  proof
    cG
    cumgr
    wcel
    #
    cA
    cB
    cpr
    #
    cE
    wcel
    #
    cB
    cC
    cpr
    #
    cE
    wcel
    #
    w3a
    #
    @3
    vi
    cv
    #
    cG
    ciedg
    cfv
    #
    cfv
    #
    wceq
    #
    vi
    @7
    cdm
    #
    wrex
    #
    @1
    vj
    cv
    #
    @7
    cfv
    #
    wceq
    #
    vj
    @10
    wrex
    #
    vf
    cv
    #
    vp
    cv
    #
    cG
    cwlks
    cfv
    #
    wbr
    #
    @16
    chash
    cfv
    #
    c2
    wceq
    #
    cA
    cc0
    @17
    cfv
    #
    wceq
    #
    cB
    c1
    @17
    cfv
    #
    wceq
    #
    cC
    c2
    @17
    cfv
    #
    wceq
    #
    w3a
    #
    w3a
    #
    vp
    wex
    vf
    wex
    #
    @0
    @2
    @4
    @11
    @0
    @4
    @11
    wi
    @2
    @0
    @4
    @11
    @0
    cG
    cuhgr
    wcel
    #
    @4
    @11
    wb
    cG
    umgruhgr
    #
    @4
    @3
    cG
    cedg
    cfv
    #
    wcel
    @31
    @11
    cE
    @33
    @3
    umgr2wlk.e
    eleq2i
    vi
    @3
    cG
    @7
    @7
    eqid
    #
    uhgredgiedgb
    syl5bb
    syl
    biimpd
    a1d
    3imp
    @0
    @2
    @4
    @15
    @0
    @2
    @15
    @4
    @0
    @2
    @15
    @0
    @31
    @2
    @15
    wb
    @32
    @2
    @1
    @33
    wcel
    @31
    @15
    cE
    @33
    @1
    umgr2wlk.e
    eleq2i
    vj
    @1
    cG
    @7
    @34
    uhgredgiedgb
    syl5bb
    syl
    biimpd
    a1dd
    3imp
    @11
    @5
    @15
    @30
    wi
    #
    @9
    @5
    @35
    wi
    vi
    @10
    @15
    @5
    @9
    @30
    @14
    @5
    @9
    @30
    wi
    #
    wi
    vj
    @10
    @5
    @14
    @36
    @5
    @14
    @9
    @30
    @12
    @6
    cs2
    #
    cvv
    cword
    #
    wcel
    #
    cA
    cB
    cC
    cs3
    #
    @38
    wcel
    #
    wa
    @5
    @14
    @9
    wa
    #
    wa
    #
    @37
    @40
    @18
    wbr
    #
    @37
    chash
    cfv
    #
    c2
    wceq
    #
    cA
    cc0
    @40
    cfv
    #
    wceq
    #
    cB
    c1
    @40
    cfv
    #
    wceq
    #
    cC
    c2
    @40
    cfv
    #
    wceq
    #
    w3a
    #
    w3a
    #
    @30
    @39
    @41
    @12
    @6
    s2cli
    cA
    cB
    cC
    s3cli
    pm3.2i
    @43
    cA
    cB
    cC
    @40
    cE
    @37
    cG
    @7
    @12
    @6
    umgr2wlk.e
    @34
    @37
    eqid
    @40
    eqid
    @0
    @2
    @4
    @42
    simpl1
    @5
    @2
    @4
    wa
    @42
    @0
    @2
    @4
    3simpc
    adantr
    @42
    @13
    @1
    wceq
    @5
    @42
    @1
    @13
    @14
    @9
    simpl
    eqcomd
    adantl
    @42
    @8
    @3
    wceq
    @5
    @42
    @3
    @8
    @14
    @9
    simpr
    eqcomd
    adantl
    umgr2adedgwlk
    @29
    @54
    vf
    vp
    @37
    @40
    @38
    @38
    @16
    @37
    wceq
    #
    @17
    @40
    wceq
    #
    wa
    @19
    @44
    @21
    @46
    @28
    @53
    @16
    @37
    @17
    @40
    @18
    breq12
    @55
    @21
    @46
    wb
    @56
    @55
    @20
    @45
    c2
    @16
    @37
    chash
    fveq2
    eqeq1d
    adantr
    @56
    @28
    @53
    wb
    @55
    @56
    @23
    @48
    @25
    @50
    @27
    @52
    @56
    @22
    @47
    cA
    cc0
    @17
    @40
    fveq1
    eqeq2d
    @56
    @24
    @49
    cB
    c1
    @17
    @40
    fveq1
    eqeq2d
    @56
    @26
    @51
    cC
    c2
    @17
    @40
    fveq1
    eqeq2d
    3anbi123d
    adantl
    3anbi123d
    spc2egv
    mpsyl
    exp32
    com12
    rexlimivw
    com13
    rexlimivw
    com12
    mp2d
end
