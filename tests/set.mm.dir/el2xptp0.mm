include "wcel.mm"
include "w3a.mm"
include "cxp.mm"
include "c1st.mm"
include "cfv.mm"
include "wceq.mm"
include "c2nd.mm"
include "wa.mm"
include "cotp.mm"
include "cop.mm"
include "xp1st.mm"
include "ad2antrl.mm"
include "3simpa.mm"
include "adantl.mm"
include "eqopi.mm"
include "syl2anc.mm"
include "simprr3.mm"
include "jca.mm"
include "wb.mm"
include "df-ot.mm"
include "eqeq2i.mm"
include "eqop.mm"
include "syl5bb.mm"
include "mpbird.mm"
include "opelxpi.mm"
include "3adant3.mm"
include "simp3.mm"
include "opelxp.mm"
include "sylanbrc.mm"
include "syl5eqel.mm"
include "adantr.mm"
include "eleq1.mm"
include "fveq2.mm"
include "fveq2d.mm"
include "ot1stg.mm"
include "sylan9eqr.mm"
include "ot2ndg.mm"
include "ot3rdg.mm"
include "3ad2ant3.mm"
include "3jca.mm"
include "impbida.mm"

theorem el2xptp0
  let cA: class A
  let cU: class U
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  let cZ: class Z


  assert |- ( ( X e. U /\ Y e. V /\ Z e. W ) -> ( ( A e. ( ( U X. V ) X. W ) /\ ( ( 1st ` ( 1st ` A ) ) = X /\ ( 2nd ` ( 1st ` A ) ) = Y /\ ( 2nd ` A ) = Z ) ) <-> A = <. X , Y , Z >. ) )

  proof
    cX
    cU
    wcel
    #
    cY
    cV
    wcel
    #
    cZ
    cW
    wcel
    #
    w3a
    #
    cA
    cU
    cV
    cxp
    #
    cW
    cxp
    #
    wcel
    #
    cA
    c1st
    cfv
    #
    c1st
    cfv
    #
    cX
    wceq
    #
    @7
    c2nd
    cfv
    #
    cY
    wceq
    #
    cA
    c2nd
    cfv
    #
    cZ
    wceq
    #
    w3a
    #
    wa
    #
    cA
    cX
    cY
    cZ
    cotp
    #
    wceq
    #
    @3
    @15
    wa
    #
    @17
    @7
    cX
    cY
    cop
    #
    wceq
    #
    @13
    wa
    #
    @18
    @20
    @13
    @18
    @7
    @4
    wcel
    #
    @9
    @11
    wa
    #
    @20
    @6
    @22
    @3
    @14
    cA
    @4
    cW
    xp1st
    ad2antrl
    @15
    @23
    @3
    @14
    @23
    @6
    @9
    @11
    @13
    3simpa
    adantl
    adantl
    @7
    cX
    cY
    cU
    cV
    eqopi
    syl2anc
    @9
    @11
    @13
    @6
    @3
    simprr3
    jca
    @6
    @17
    @21
    wb
    @3
    @14
    @17
    cA
    @19
    cZ
    cop
    #
    wceq
    @6
    @21
    @16
    @24
    cA
    cX
    cY
    cZ
    df-ot
    #
    eqeq2i
    cA
    @19
    cZ
    @4
    cW
    eqop
    syl5bb
    ad2antrl
    mpbird
    @3
    @17
    wa
    #
    @6
    @14
    @26
    @6
    @16
    @5
    wcel
    #
    @3
    @27
    @17
    @3
    @16
    @24
    @5
    @25
    @3
    @19
    @4
    wcel
    #
    @2
    @24
    @5
    wcel
    @0
    @1
    @28
    @2
    cX
    cY
    cU
    cV
    opelxpi
    3adant3
    @0
    @1
    @2
    simp3
    @19
    cZ
    @4
    cW
    opelxp
    sylanbrc
    syl5eqel
    adantr
    @17
    @6
    @27
    wb
    @3
    cA
    @16
    @5
    eleq1
    adantl
    mpbird
    @26
    @9
    @11
    @13
    @17
    @3
    @8
    @16
    c1st
    cfv
    #
    c1st
    cfv
    cX
    @17
    @7
    @29
    c1st
    cA
    @16
    c1st
    fveq2
    #
    fveq2d
    cX
    cY
    cZ
    cU
    cV
    cW
    ot1stg
    sylan9eqr
    @17
    @3
    @10
    @29
    c2nd
    cfv
    cY
    @17
    @7
    @29
    c2nd
    @30
    fveq2d
    cX
    cY
    cZ
    cU
    cV
    cW
    ot2ndg
    sylan9eqr
    @17
    @3
    @12
    @16
    c2nd
    cfv
    #
    cZ
    cA
    @16
    c2nd
    fveq2
    @2
    @0
    @31
    cZ
    wceq
    @1
    cX
    cY
    cZ
    cW
    ot3rdg
    3ad2ant3
    sylan9eqr
    3jca
    jca
    impbida
end
