include "crngo.mm"
include "wcel.mm"
include "w3a.mm"
include "co.mm"
include "cgi.mm"
include "cfv.mm"
include "wceq.mm"
include "wi.mm"
include "crn.mm"
include "c1st.mm"
include "rneqi.mm"
include "eqtri.mm"
include "eqid.mm"
include "rngo1cl.mm"
include "rngonegcl.mm"
include "mpdan.mm"
include "rngoass.mm"
include "3exp2.mm"
include "com24.mm"
include "com34.mm"
include "mpd.mm"
include "3imp.mm"
include "wa.mm"
include "rngocl.mm"
include "3expb.mm"
include "rngonegmn1r.mm"
include "syldan.mm"
include "3impb.mm"
include "3adant2.mm"
include "oveq2d.mm"
include "3eqtr4d.mm"

theorem rngonegrmul
  let cA: class A
  let cB: class B
  let cR: class R
  let cG: class G
  let cH: class H
  let cN: class N
  let cX: class X
  assume ringnegmul.1: |- G = ( 1st ` R )
  assume ringnegmul.2: |- H = ( 2nd ` R )
  assume ringnegmul.3: |- X = ran G
  assume ringnegmul.4: |- N = ( inv ` G )


  assert |- ( ( R e. RingOps /\ A e. X /\ B e. X ) -> ( N ` ( A H B ) ) = ( A H ( N ` B ) ) )

  proof
    cR
    crngo
    wcel
    #
    cA
    cX
    wcel
    #
    cB
    cX
    wcel
    #
    w3a
    #
    cA
    cB
    cH
    co
    #
    cH
    cgi
    cfv
    #
    cN
    cfv
    #
    cH
    co
    #
    cA
    cB
    @6
    cH
    co
    #
    cH
    co
    #
    @4
    cN
    cfv
    #
    cA
    cB
    cN
    cfv
    #
    cH
    co
    @0
    @1
    @2
    @7
    @9
    wceq
    #
    @0
    @6
    cX
    wcel
    #
    @1
    @2
    @12
    wi
    wi
    @0
    @5
    cX
    wcel
    @13
    cR
    @5
    cH
    cX
    cX
    cG
    crn
    cR
    c1st
    cfv
    #
    crn
    ringnegmul.3
    cG
    @14
    ringnegmul.1
    rneqi
    eqtri
    ringnegmul.2
    @5
    eqid
    #
    rngo1cl
    @5
    cR
    cG
    cN
    cX
    ringnegmul.1
    ringnegmul.3
    ringnegmul.4
    rngonegcl
    mpdan
    @0
    @13
    @2
    @1
    @12
    @0
    @1
    @2
    @13
    @12
    @0
    @1
    @2
    @13
    @12
    cA
    cB
    @6
    cR
    cG
    cH
    cX
    ringnegmul.1
    ringnegmul.2
    ringnegmul.3
    rngoass
    3exp2
    com24
    com34
    mpd
    3imp
    @0
    @1
    @2
    @10
    @7
    wceq
    #
    @0
    @1
    @2
    wa
    @4
    cX
    wcel
    #
    @16
    @0
    @1
    @2
    @17
    cA
    cB
    cR
    cG
    cH
    cX
    ringnegmul.1
    ringnegmul.2
    ringnegmul.3
    rngocl
    3expb
    @4
    cR
    @5
    cG
    cH
    cN
    cX
    ringnegmul.1
    ringnegmul.2
    ringnegmul.3
    ringnegmul.4
    @15
    rngonegmn1r
    syldan
    3impb
    @3
    @11
    @8
    cA
    cH
    @0
    @2
    @11
    @8
    wceq
    @1
    cB
    cR
    @5
    cG
    cH
    cN
    cX
    ringnegmul.1
    ringnegmul.2
    ringnegmul.3
    ringnegmul.4
    @15
    rngonegmn1r
    3adant2
    oveq2d
    3eqtr4d
end
