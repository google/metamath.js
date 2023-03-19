include "crngo.mm"
include "wcel.mm"
include "cidl.mm"
include "cfv.mm"
include "wa.mm"
include "wceq.mm"
include "wss.mm"
include "idlss.mm"
include "adantr.mm"
include "cv.mm"
include "co.mm"
include "crn.mm"
include "c1st.mm"
include "rneqi.mm"
include "eqtri.mm"
include "rngolidm.mm"
include "ad2ant2rl.mm"
include "idlrmulcl.mm"
include "eqeltrrd.mm"
include "expr.mm"
include "ssrdv.mm"
include "eqssd.mm"
include "ex.mm"
include "rngo1cl.mm"
include "eleq2.mm"
include "syl5ibrcom.mm"
include "impbid.mm"

theorem 1idl
  let cR: class R
  let cU: class U
  let cG: class G
  let cH: class H
  let cI: class I
  let cX: class X
  let vx: setvar x
  assume 1idl.1: |- G = ( 1st ` R )
  assume 1idl.2: |- H = ( 2nd ` R )
  assume 1idl.3: |- X = ran G
  assume 1idl.4: |- U = ( GId ` H )


  assert |- ( ( R e. RingOps /\ I e. ( Idl ` R ) ) -> ( U e. I <-> I = X ) )

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
    cU
    cI
    wcel
    #
    cI
    cX
    wceq
    #
    @2
    @3
    @4
    @2
    @3
    wa
    #
    cI
    cX
    @2
    cI
    cX
    wss
    @3
    cR
    cG
    cI
    cX
    1idl.1
    1idl.3
    idlss
    adantr
    @5
    vx
    cX
    cI
    @2
    @3
    vx
    cv
    #
    cX
    wcel
    #
    @6
    cI
    wcel
    @2
    @3
    @7
    wa
    wa
    cU
    @6
    cH
    co
    #
    @6
    cI
    @0
    @7
    @8
    @6
    wceq
    @1
    @3
    @6
    cR
    cU
    cH
    cX
    1idl.2
    cX
    cG
    crn
    cR
    c1st
    cfv
    #
    crn
    1idl.3
    cG
    @9
    1idl.1
    rneqi
    eqtri
    #
    1idl.4
    rngolidm
    ad2ant2rl
    cU
    @6
    cR
    cG
    cH
    cI
    cX
    1idl.1
    1idl.2
    1idl.3
    idlrmulcl
    eqeltrrd
    expr
    ssrdv
    eqssd
    ex
    @2
    @3
    @4
    cU
    cX
    wcel
    #
    @0
    @11
    @1
    cR
    cU
    cH
    cX
    @10
    1idl.2
    1idl.4
    rngo1cl
    adantr
    cI
    cX
    cU
    eleq2
    syl5ibrcom
    impbid
end
