include "crngo.mm"
include "wcel.mm"
include "cv.mm"
include "co.mm"
include "wceq.mm"
include "wrex.mm"
include "wi.mm"
include "w3a.mm"
include "oveq2.mm"
include "wa.mm"
include "simpl1.mm"
include "simpr1.mm"
include "simpr3.mm"
include "simpl3.mm"
include "rngoass.mm"
include "syl13anc.mm"
include "eqtr.mm"
include "ex.mm"
include "rngorz.mm"
include "3adant3.mm"
include "crn.mm"
include "c1st.mm"
include "cfv.mm"
include "rneqi.mm"
include "eqtri.mm"
include "rngolidm.mm"
include "3adant2.mm"
include "simp1.mm"
include "simp2.mm"
include "simp3.mm"
include "3eqtr3d.mm"
include "a1d.mm"
include "3exp.mm"
include "com14.mm"
include "com13.mm"
include "sylc.mm"
include "com15.mm"
include "com24.mm"
include "syl.mm"
include "eqcoms.mm"
include "com25.mm"
include "oveq1.mm"
include "syl11.mm"
include "3imp.mm"
include "syl6.mm"
include "3imp1.mm"
include "mpd.mm"
include "3exp1.mm"
include "syl5com.mm"
include "rexlimiv.mm"

theorem zerdivemp1x
  let cA: class A
  let cB: class B
  let cR: class R
  let cU: class U
  let cG: class G
  let cH: class H
  let cX: class X
  let cZ: class Z
  let va: setvar a
  assume zerdivempx.1: |- G = ( 1st ` R )
  assume zerdivempx.2: |- H = ( 2nd ` R )
  assume zerdivempx.3: |- Z = ( GId ` G )
  assume zerdivempx.4: |- X = ran G
  assume zerdivempx.5: |- U = ( GId ` H )

  disjoint A a
  disjoint B a
  disjoint H a
  disjoint R a
  disjoint X a
  disjoint Z a
  assert |- ( ( R e. RingOps /\ A e. X /\ E. a e. X ( a H A ) = U ) -> ( B e. X -> ( ( A H B ) = Z -> B = Z ) ) )

  proof
    cR
    crngo
    wcel
    #
    cA
    cX
    wcel
    #
    va
    cv
    #
    cA
    cH
    co
    #
    cU
    wceq
    #
    va
    cX
    wrex
    #
    cB
    cX
    wcel
    #
    cA
    cB
    cH
    co
    #
    cZ
    wceq
    #
    cB
    cZ
    wceq
    #
    wi
    wi
    #
    @5
    @1
    @0
    @10
    @4
    @1
    @0
    @10
    wi
    #
    wi
    va
    cX
    @2
    cX
    wcel
    #
    @4
    @1
    @11
    @8
    @0
    @6
    @12
    @4
    @1
    w3a
    #
    @9
    @8
    @2
    @7
    cH
    co
    #
    @2
    cZ
    cH
    co
    #
    wceq
    #
    @0
    @6
    @13
    @9
    wi
    wi
    @7
    cZ
    @2
    cH
    oveq2
    @0
    @16
    @6
    @13
    @9
    @0
    @16
    @6
    w3a
    #
    @13
    wa
    #
    @3
    cB
    cH
    co
    #
    @14
    wceq
    #
    @9
    @18
    @0
    @12
    @1
    @6
    @20
    @0
    @16
    @6
    @13
    simpl1
    @17
    @12
    @4
    @1
    simpr1
    @17
    @12
    @4
    @1
    simpr3
    @0
    @16
    @6
    @13
    simpl3
    @2
    cA
    cB
    cR
    cG
    cH
    cX
    zerdivempx.1
    zerdivempx.2
    zerdivempx.4
    rngoass
    syl13anc
    @0
    @16
    @6
    @13
    @20
    @9
    wi
    @20
    @16
    @6
    @13
    @0
    @9
    @20
    @16
    @19
    @15
    wceq
    #
    @6
    @13
    @0
    @9
    wi
    #
    wi
    wi
    @20
    @16
    @21
    @19
    @14
    @15
    eqtr
    ex
    @13
    @6
    @21
    @22
    @12
    @4
    @1
    @6
    @21
    @22
    wi
    wi
    #
    @19
    cU
    cB
    cH
    co
    #
    wceq
    #
    @12
    @1
    @23
    wi
    @4
    @25
    @21
    @1
    @6
    @12
    @22
    @21
    @1
    @6
    @12
    @22
    wi
    wi
    wi
    #
    wi
    @24
    @19
    @24
    @19
    wceq
    #
    @21
    @26
    @27
    @21
    wa
    @24
    @15
    wceq
    #
    @26
    @24
    @19
    @15
    eqtr
    @28
    @12
    @6
    @1
    @22
    @0
    @12
    @6
    @1
    @28
    @9
    @0
    @12
    @6
    @1
    @28
    @9
    wi
    #
    wi
    #
    @0
    @12
    @6
    w3a
    @15
    cZ
    wceq
    #
    @24
    cB
    wceq
    #
    @30
    @0
    @12
    @31
    @6
    @2
    cR
    cG
    cH
    cX
    cZ
    zerdivempx.3
    zerdivempx.4
    zerdivempx.1
    zerdivempx.2
    rngorz
    3adant3
    @0
    @6
    @32
    @12
    cB
    cR
    cU
    cH
    cX
    zerdivempx.2
    cX
    cG
    crn
    cR
    c1st
    cfv
    #
    crn
    zerdivempx.4
    cG
    @33
    zerdivempx.1
    rneqi
    eqtri
    zerdivempx.5
    rngolidm
    3adant2
    @1
    @32
    @31
    @29
    @28
    @32
    @31
    @1
    @9
    @28
    @32
    @31
    @1
    @9
    wi
    @28
    @32
    @31
    w3a
    #
    @9
    @1
    @34
    @24
    @15
    cB
    cZ
    @28
    @32
    @31
    simp1
    @28
    @32
    @31
    simp2
    @28
    @32
    @31
    simp3
    3eqtr3d
    a1d
    3exp
    com14
    com13
    sylc
    3exp
    com15
    com24
    syl
    ex
    eqcoms
    com25
    @3
    cU
    cB
    cH
    oveq1
    syl11
    3imp
    com13
    syl6
    com15
    3imp1
    mpd
    3exp1
    syl5com
    com14
    3exp
    rexlimiv
    com13
    3imp
end
