include "wcel.mm"
include "w3a.mm"
include "wa.mm"
include "cotp.mm"
include "cvv.mm"
include "cv.mm"
include "cc0.mm"
include "c1st.mm"
include "cfv.mm"
include "cop.mm"
include "csubstr.mm"
include "co.mm"
include "c2nd.mm"
include "cconcat.mm"
include "chash.mm"
include "csplice.mm"
include "cmpt2.mm"
include "wceq.mm"
include "df-splice.mm"
include "a1i.mm"
include "simprl.mm"
include "fveq2.mm"
include "fveq2d.mm"
include "adantl.mm"
include "ot1stg.mm"
include "sylan9eqr.mm"
include "opeq2d.mm"
include "oveq12d.mm"
include "ot3rdg.mm"
include "3ad2ant3.mm"
include "ot2ndg.mm"
include "opeq12d.mm"
include "elex.mm"
include "adantr.mm"
include "otex.mm"
include "ovexd.mm"
include "ovmpt2d.mm"

theorem splval
  let cR: class R
  let cS: class S
  let cT: class T
  let cF: class F
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  let vb: setvar b
  let vs: setvar s


  assert |- ( ( S e. V /\ ( F e. W /\ T e. X /\ R e. Y ) ) -> ( S splice <. F , T , R >. ) = ( ( ( S substr <. 0 , F >. ) ++ R ) ++ ( S substr <. T , ( # ` S ) >. ) ) )

  proof
    cS
    cV
    wcel
    #
    cF
    cW
    wcel
    #
    cT
    cX
    wcel
    #
    cR
    cY
    wcel
    #
    w3a
    #
    wa
    #
    vs
    vb
    cS
    cF
    cT
    cR
    cotp
    #
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
    @8
    c2nd
    cfv
    #
    cconcat
    co
    #
    @7
    @9
    c2nd
    cfv
    #
    @7
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
    cS
    cc0
    cF
    cop
    #
    csubstr
    co
    #
    cR
    cconcat
    co
    #
    cS
    cT
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
    csplice
    cvv
    csplice
    vs
    vb
    cvv
    cvv
    @19
    cmpt2
    wceq
    @5
    vs
    vb
    df-splice
    a1i
    @5
    @7
    cS
    wceq
    #
    @8
    @6
    wceq
    #
    wa
    #
    wa
    #
    @14
    @22
    @18
    @25
    cconcat
    @29
    @12
    @21
    @13
    cR
    cconcat
    @29
    @7
    cS
    @11
    @20
    csubstr
    @5
    @26
    @27
    simprl
    #
    @29
    @10
    cF
    cc0
    @28
    @5
    @10
    @6
    c1st
    cfv
    #
    c1st
    cfv
    #
    cF
    @27
    @10
    @32
    wceq
    @26
    @27
    @9
    @31
    c1st
    @8
    @6
    c1st
    fveq2
    #
    fveq2d
    adantl
    @4
    @32
    cF
    wceq
    @0
    cF
    cT
    cR
    cW
    cX
    cY
    ot1stg
    adantl
    sylan9eqr
    opeq2d
    oveq12d
    @28
    @5
    @13
    @6
    c2nd
    cfv
    #
    cR
    @27
    @13
    @34
    wceq
    @26
    @8
    @6
    c2nd
    fveq2
    adantl
    @4
    @34
    cR
    wceq
    #
    @0
    @3
    @1
    @35
    @2
    cF
    cT
    cR
    cY
    ot3rdg
    3ad2ant3
    adantl
    sylan9eqr
    oveq12d
    @29
    @7
    cS
    @17
    @24
    csubstr
    @30
    @29
    @15
    cT
    @16
    @23
    @28
    @5
    @15
    @31
    c2nd
    cfv
    #
    cT
    @27
    @15
    @36
    wceq
    @26
    @27
    @9
    @31
    c2nd
    @33
    fveq2d
    adantl
    @4
    @36
    cT
    wceq
    @0
    cF
    cT
    cR
    cW
    cX
    cY
    ot2ndg
    adantl
    sylan9eqr
    @29
    @7
    cS
    chash
    @30
    fveq2d
    opeq12d
    oveq12d
    oveq12d
    @0
    cS
    cvv
    wcel
    @4
    cS
    cV
    elex
    adantr
    @6
    cvv
    wcel
    @5
    cF
    cT
    cR
    otex
    a1i
    @5
    @22
    @25
    cconcat
    ovexd
    ovmpt2d
end
