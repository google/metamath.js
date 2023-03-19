include "crngo.mm"
include "wcel.mm"
include "cidl.mm"
include "cfv.mm"
include "wa.mm"
include "c2nd.mm"
include "cgi.mm"
include "co.mm"
include "crn.mm"
include "wss.mm"
include "wceq.mm"
include "eqid.mm"
include "idlss.mm"
include "ssel2.mm"
include "rngonegmn1l.mm"
include "sylan2.mm"
include "anassrs.mm"
include "syldanl.mm"
include "c1st.mm"
include "rneqi.mm"
include "rngo1cl.mm"
include "rngonegcl.mm"
include "mpdan.mm"
include "ad2antrr.mm"
include "idllmulcl.mm"
include "eqeltrd.mm"

theorem idlnegcl
  let cA: class A
  let cR: class R
  let cG: class G
  let cI: class I
  let cN: class N
  assume idlnegcl.1: |- G = ( 1st ` R )
  assume idlnegcl.2: |- N = ( inv ` G )


  assert |- ( ( ( R e. RingOps /\ I e. ( Idl ` R ) ) /\ A e. I ) -> ( N ` A ) e. I )

  proof
    cR
    crngo
    wcel
    #
    cI
    cR
    cidl
    cfv
    wcel
    #
    wa
    #
    cA
    cI
    wcel
    #
    wa
    #
    cA
    cN
    cfv
    #
    cR
    c2nd
    cfv
    #
    cgi
    cfv
    #
    cN
    cfv
    #
    cA
    @6
    co
    #
    cI
    @0
    @1
    cI
    cG
    crn
    #
    wss
    #
    @3
    @5
    @9
    wceq
    #
    cR
    cG
    cI
    @10
    idlnegcl.1
    @10
    eqid
    #
    idlss
    @0
    @11
    @3
    @12
    @11
    @3
    wa
    @0
    cA
    @10
    wcel
    @12
    cI
    @10
    cA
    ssel2
    cA
    cR
    @7
    cG
    @6
    cN
    @10
    idlnegcl.1
    @6
    eqid
    #
    @13
    idlnegcl.2
    @7
    eqid
    #
    rngonegmn1l
    sylan2
    anassrs
    syldanl
    @4
    @8
    @10
    wcel
    #
    @9
    cI
    wcel
    #
    @0
    @16
    @1
    @3
    @0
    @7
    @10
    wcel
    @16
    cR
    @7
    @6
    @10
    cG
    cR
    c1st
    cfv
    idlnegcl.1
    rneqi
    @14
    @15
    rngo1cl
    @7
    cR
    cG
    cN
    @10
    idlnegcl.1
    @13
    idlnegcl.2
    rngonegcl
    mpdan
    ad2antrr
    @2
    @3
    @16
    @17
    cA
    @8
    cR
    cG
    @6
    cI
    @10
    idlnegcl.1
    @14
    @13
    idllmulcl
    anassrs
    mpdan
    eqeltrd
end
