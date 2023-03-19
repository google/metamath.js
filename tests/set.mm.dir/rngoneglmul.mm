include "crngo.mm"
include "wcel.mm"
include "w3a.mm"
include "cgi.mm"
include "cfv.mm"
include "co.mm"
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
include "mpd.mm"
include "3imp.mm"
include "rngonegmn1l.mm"
include "3adant3.mm"
include "oveq1d.mm"
include "wa.mm"
include "rngocl.mm"
include "3expb.mm"
include "syldan.mm"
include "3impb.mm"
include "3eqtr4rd.mm"

theorem rngoneglmul
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


  assert |- ( ( R e. RingOps /\ A e. X /\ B e. X ) -> ( N ` ( A H B ) ) = ( ( N ` A ) H B ) )

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
    cH
    cgi
    cfv
    #
    cN
    cfv
    #
    cA
    cH
    co
    #
    cB
    cH
    co
    #
    @5
    cA
    cB
    cH
    co
    #
    cH
    co
    #
    cA
    cN
    cfv
    #
    cB
    cH
    co
    @8
    cN
    cfv
    #
    @0
    @1
    @2
    @7
    @9
    wceq
    #
    @0
    @5
    cX
    wcel
    #
    @1
    @2
    @12
    wi
    wi
    @0
    @4
    cX
    wcel
    @13
    cR
    @4
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
    @4
    eqid
    #
    rngo1cl
    @4
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
    @1
    @2
    @12
    @5
    cA
    cB
    cR
    cG
    cH
    cX
    ringnegmul.1
    ringnegmul.2
    ringnegmul.3
    rngoass
    3exp2
    mpd
    3imp
    @3
    @10
    @6
    cB
    cH
    @0
    @1
    @10
    @6
    wceq
    @2
    cA
    cR
    @4
    cG
    cH
    cN
    cX
    ringnegmul.1
    ringnegmul.2
    ringnegmul.3
    ringnegmul.4
    @15
    rngonegmn1l
    3adant3
    oveq1d
    @0
    @1
    @2
    @11
    @9
    wceq
    #
    @0
    @1
    @2
    wa
    @8
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
    @8
    cR
    @4
    cG
    cH
    cN
    cX
    ringnegmul.1
    ringnegmul.2
    ringnegmul.3
    ringnegmul.4
    @15
    rngonegmn1l
    syldan
    3impb
    3eqtr4rd
end
