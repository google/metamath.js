include "crngo.mm"
include "wcel.mm"
include "wceq.mm"
include "csn.mm"
include "cgi.mm"
include "cfv.mm"
include "cvv.mm"
include "fvex.mm"
include "eqeltri.mm"
include "snid.mm"
include "eleq1.mm"
include "mpbii.mm"
include "cidl.mm"
include "wb.mm"
include "0idl.mm"
include "1idl.mm"
include "mpdan.mm"
include "syl5ib.mm"
include "eqcom.mm"
include "syl6ib.mm"
include "crn.mm"
include "c1st.mm"
include "rneqi.mm"
include "eqtri.mm"
include "rngo1cl.mm"
include "eleq2.mm"
include "elsni.mm"
include "eqcomd.mm"
include "syl6bi.mm"
include "syl5com.mm"
include "impbid.mm"

theorem 0rngo
  let cR: class R
  let cU: class U
  let cG: class G
  let cH: class H
  let cX: class X
  let cZ: class Z
  assume 0ring.1: |- G = ( 1st ` R )
  assume 0ring.2: |- H = ( 2nd ` R )
  assume 0ring.3: |- X = ran G
  assume 0ring.4: |- Z = ( GId ` G )
  assume 0ring.5: |- U = ( GId ` H )


  assert |- ( R e. RingOps -> ( Z = U <-> X = { Z } ) )

  proof
    cR
    crngo
    wcel
    #
    cZ
    cU
    wceq
    #
    cX
    cZ
    csn
    #
    wceq
    #
    @0
    @1
    @2
    cX
    wceq
    #
    @3
    @1
    cU
    @2
    wcel
    #
    @0
    @4
    @1
    cZ
    @2
    wcel
    @5
    cZ
    cZ
    cG
    cgi
    cfv
    cvv
    0ring.4
    cG
    cgi
    fvex
    eqeltri
    snid
    cZ
    cU
    @2
    eleq1
    mpbii
    @0
    @2
    cR
    cidl
    cfv
    wcel
    @5
    @4
    wb
    cR
    cG
    cZ
    0ring.1
    0ring.4
    0idl
    cR
    cU
    cG
    cH
    @2
    cX
    0ring.1
    0ring.2
    0ring.3
    0ring.5
    1idl
    mpdan
    syl5ib
    @2
    cX
    eqcom
    syl6ib
    @0
    cU
    cX
    wcel
    #
    @3
    @1
    cR
    cU
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
    0ring.3
    cG
    @7
    0ring.1
    rneqi
    eqtri
    0ring.2
    0ring.5
    rngo1cl
    @3
    @6
    @5
    @1
    cX
    @2
    cU
    eleq2
    @5
    cU
    cZ
    cU
    cZ
    elsni
    eqcomd
    syl6bi
    syl5com
    impbid
end
