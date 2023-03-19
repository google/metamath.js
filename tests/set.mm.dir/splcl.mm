include "cword.mm"
include "wcel.mm"
include "wa.mm"
include "cotp.mm"
include "csplice.mm"
include "co.mm"
include "cc0.mm"
include "c1st.mm"
include "cfv.mm"
include "cop.mm"
include "csubstr.mm"
include "c2nd.mm"
include "cconcat.mm"
include "chash.mm"
include "wceq.mm"
include "cvv.mm"
include "elex.mm"
include "otex.mm"
include "cv.mm"
include "id.mm"
include "fveq2.mm"
include "fveq2d.mm"
include "opeq2d.mm"
include "oveqan12d.mm"
include "simpr.mm"
include "oveq12d.mm"
include "simpl.mm"
include "opeq12d.mm"
include "df-splice.mm"
include "ovex.mm"
include "ovmpt2a.mm"
include "sylancl.mm"
include "adantr.mm"
include "swrdcl.mm"
include "ot3rdg.mm"
include "adantl.mm"
include "eqeltrd.mm"
include "ccatcl.mm"
include "syl2anc.mm"

theorem splcl
  let cA: class A
  let cR: class R
  let cS: class S
  let cT: class T
  let cF: class F
  let vb: setvar b
  let vs: setvar s
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y


  assert |- ( ( S e. Word A /\ R e. Word A ) -> ( S splice <. F , T , R >. ) e. Word A )

  proof
    cS
    cA
    cword
    #
    wcel
    #
    cR
    @0
    wcel
    #
    wa
    #
    cS
    cF
    cT
    cR
    cotp
    #
    csplice
    co
    #
    cS
    cc0
    @4
    c1st
    cfv
    #
    c1st
    cfv
    #
    cop
    #
    csubstr
    co
    #
    @4
    c2nd
    cfv
    #
    cconcat
    co
    #
    cS
    @6
    c2nd
    cfv
    #
    cS
    chash
    cfv
    #
    cop
    #
    csubstr
    co
    #
    cconcat
    co
    #
    @0
    @1
    @5
    @16
    wceq
    #
    @2
    @1
    cS
    cvv
    wcel
    @4
    cvv
    wcel
    @17
    cS
    @0
    elex
    cF
    cT
    cR
    otex
    vs
    vb
    cS
    @4
    cvv
    cvv
    vs
    cv
    #
    cc0
    vb
    cv
    #
    c1st
    cfv
    #
    c1st
    cfv
    #
    cop
    #
    csubstr
    co
    #
    @19
    c2nd
    cfv
    #
    cconcat
    co
    #
    @18
    @20
    c2nd
    cfv
    #
    @18
    chash
    cfv
    #
    cop
    #
    csubstr
    co
    #
    cconcat
    co
    @16
    csplice
    @18
    cS
    wceq
    #
    @19
    @4
    wceq
    #
    wa
    #
    @25
    @11
    @29
    @15
    cconcat
    @32
    @23
    @9
    @24
    @10
    cconcat
    @30
    @31
    @18
    cS
    @22
    @8
    csubstr
    @30
    id
    @31
    @21
    @7
    cc0
    @31
    @20
    @6
    c1st
    @19
    @4
    c1st
    fveq2
    fveq2d
    opeq2d
    oveqan12d
    @32
    @19
    @4
    c2nd
    @30
    @31
    simpr
    #
    fveq2d
    oveq12d
    @32
    @18
    cS
    @28
    @14
    csubstr
    @30
    @31
    simpl
    #
    @32
    @26
    @12
    @27
    @13
    @32
    @20
    @6
    c2nd
    @32
    @19
    @4
    c1st
    @33
    fveq2d
    fveq2d
    @32
    @18
    cS
    chash
    @34
    fveq2d
    opeq12d
    oveq12d
    oveq12d
    vs
    vb
    df-splice
    @11
    @15
    cconcat
    ovex
    ovmpt2a
    sylancl
    adantr
    @3
    @11
    @0
    wcel
    #
    @15
    @0
    wcel
    #
    @16
    @0
    wcel
    @3
    @9
    @0
    wcel
    #
    @10
    @0
    wcel
    @35
    @1
    @37
    @2
    cA
    cS
    cc0
    @7
    swrdcl
    adantr
    @3
    @10
    cR
    @0
    @2
    @10
    cR
    wceq
    @1
    cF
    cT
    cR
    @0
    ot3rdg
    adantl
    @1
    @2
    simpr
    eqeltrd
    cA
    @9
    @10
    ccatcl
    syl2anc
    @1
    @36
    @2
    cA
    cS
    @12
    @13
    swrdcl
    adantr
    cA
    @11
    @15
    ccatcl
    syl2anc
    eqeltrd
end
