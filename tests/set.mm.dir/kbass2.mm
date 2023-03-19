include "chil.mm"
include "wcel.mm"
include "w3a.mm"
include "cbr.mm"
include "cfv.mm"
include "chft.mm"
include "co.mm"
include "ck.mm"
include "ccom.mm"
include "wfn.mm"
include "cv.mm"
include "cmul.mm"
include "cmpt.mm"
include "ovex.mm"
include "eqid.mm"
include "fnmpti.mm"
include "wceq.mm"
include "wa.mm"
include "cc.mm"
include "wf.mm"
include "bracl.mm"
include "brafn.mm"
include "hfmmval.mm"
include "syl2an.mm"
include "3impa.mm"
include "fneq1d.mm"
include "mpbiri.mm"
include "kbop.mm"
include "fco.mm"
include "3impb.mm"
include "ffn.mm"
include "syl.mm"
include "csp.mm"
include "simpl1.mm"
include "simpl2.mm"
include "braval.mm"
include "syl2anc.mm"
include "simpl3.mm"
include "simpr.mm"
include "oveq12d.mm"
include "hicl.mm"
include "eqeltrd.mm"
include "hfmval.mm"
include "syl3anc.mm"
include "csm.mm"
include "ax-his3.mm"
include "3adant1.mm"
include "fvco3.mm"
include "sylan.mm"
include "kbval.mm"
include "fveq2d.mm"
include "hvmulcl.mm"
include "3eqtrd.mm"
include "mulcomd.mm"
include "3eqtr4d.mm"
include "eqfnfvd.mm"

theorem kbass2
  let cA: class A
  let cB: class B
  let cC: class C
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let cD: class D
  let cS: class S
  let vt: setvar t
  let vu: setvar u
  let cT: class T
  let cU: class U


  assert |- ( ( A e. ~H /\ B e. ~H /\ C e. ~H ) -> ( ( ( bra ` A ) ` B ) .fn ( bra ` C ) ) = ( ( bra ` A ) o. ( B ketbra C ) ) )

  proof
    cA
    chil
    wcel
    #
    cB
    chil
    wcel
    #
    cC
    chil
    wcel
    #
    w3a
    #
    vx
    chil
    cB
    cA
    cbr
    cfv
    #
    cfv
    #
    cC
    cbr
    cfv
    #
    chft
    co
    #
    @4
    cB
    cC
    ck
    co
    #
    ccom
    #
    @3
    @7
    chil
    wfn
    vx
    chil
    @5
    vx
    cv
    #
    @6
    cfv
    #
    cmul
    co
    #
    cmpt
    #
    chil
    wfn
    vx
    chil
    @12
    @13
    @5
    @11
    cmul
    ovex
    @13
    eqid
    fnmpti
    @3
    chil
    @7
    @13
    @0
    @1
    @2
    @7
    @13
    wceq
    #
    @0
    @1
    wa
    @5
    cc
    wcel
    #
    chil
    cc
    @6
    wf
    #
    @14
    @2
    cA
    cB
    bracl
    cC
    brafn
    #
    vx
    @5
    @6
    hfmmval
    syl2an
    3impa
    fneq1d
    mpbiri
    @3
    chil
    cc
    @9
    wf
    #
    @9
    chil
    wfn
    @0
    @1
    @2
    @18
    @0
    chil
    cc
    @4
    wf
    chil
    chil
    @8
    wf
    #
    @18
    @1
    @2
    wa
    cA
    brafn
    cB
    cC
    kbop
    #
    chil
    chil
    cc
    @4
    @8
    fco
    syl2an
    3impb
    chil
    cc
    @9
    ffn
    syl
    @3
    @10
    chil
    wcel
    #
    wa
    #
    @12
    cB
    cA
    csp
    co
    #
    @10
    cC
    csp
    co
    #
    cmul
    co
    #
    @10
    @7
    cfv
    #
    @10
    @9
    cfv
    #
    @22
    @5
    @23
    @11
    @24
    cmul
    @22
    @0
    @1
    @5
    @23
    wceq
    @0
    @1
    @2
    @21
    simpl1
    #
    @0
    @1
    @2
    @21
    simpl2
    #
    cA
    cB
    braval
    syl2anc
    #
    @22
    @2
    @21
    @11
    @24
    wceq
    @0
    @1
    @2
    @21
    simpl3
    #
    @3
    @21
    simpr
    #
    cC
    @10
    braval
    syl2anc
    oveq12d
    @22
    @15
    @16
    @21
    @26
    @12
    wceq
    @22
    @5
    @23
    cc
    @30
    @22
    @1
    @0
    @23
    cc
    wcel
    @29
    @28
    cB
    cA
    hicl
    syl2anc
    #
    eqeltrd
    @22
    @2
    @16
    @31
    @17
    syl
    @32
    @5
    @10
    @6
    hfmval
    syl3anc
    @22
    @24
    cB
    csm
    co
    #
    cA
    csp
    co
    #
    @24
    @23
    cmul
    co
    #
    @27
    @25
    @22
    @24
    cc
    wcel
    #
    @1
    @0
    @35
    @36
    wceq
    @22
    @21
    @2
    @37
    @32
    @31
    @10
    cC
    hicl
    syl2anc
    #
    @29
    @28
    @24
    cB
    cA
    ax-his3
    syl3anc
    @22
    @27
    @10
    @8
    cfv
    #
    @4
    cfv
    #
    @34
    @4
    cfv
    #
    @35
    @3
    @19
    @21
    @27
    @40
    wceq
    @1
    @2
    @19
    @0
    @20
    3adant1
    chil
    chil
    @10
    @4
    @8
    fvco3
    sylan
    @22
    @39
    @34
    @4
    @22
    @1
    @2
    @21
    @39
    @34
    wceq
    @29
    @31
    @32
    cB
    cC
    @10
    kbval
    syl3anc
    fveq2d
    @22
    @0
    @34
    chil
    wcel
    #
    @41
    @35
    wceq
    @28
    @22
    @37
    @1
    @42
    @38
    @29
    @24
    cB
    hvmulcl
    syl2anc
    cA
    @34
    braval
    syl2anc
    3eqtrd
    @22
    @23
    @24
    @33
    @38
    mulcomd
    3eqtr4d
    3eqtr4d
    eqfnfvd
end
