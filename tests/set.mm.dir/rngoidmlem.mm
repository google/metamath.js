include "crngo.mm"
include "wcel.mm"
include "co.mm"
include "wceq.mm"
include "wa.mm"
include "wi.mm"
include "crn.mm"
include "cmndo.mm"
include "cmagm.mm"
include "cexid.mm"
include "cin.mm"
include "rngomndo.mm"
include "mndomgmid.mm"
include "eqid.mm"
include "cmpidelt.mm"
include "ex.mm"
include "3syl.mm"
include "c1st.mm"
include "cfv.mm"
include "wb.mm"
include "rngorn1eq.mm"
include "eqtr.mm"
include "simpl.mm"
include "eleq2d.mm"
include "imbi1d.mm"
include "syl.mm"
include "mpan.mm"
include "mpcom.mm"
include "mpbird.mm"
include "imp.mm"

theorem rngoidmlem
  let cA: class A
  let cR: class R
  let cU: class U
  let cH: class H
  let cX: class X
  assume uridm.1: |- H = ( 2nd ` R )
  assume uridm.2: |- X = ran ( 1st ` R )
  assume uridm.3: |- U = ( GId ` H )


  assert |- ( ( R e. RingOps /\ A e. X ) -> ( ( U H A ) = A /\ ( A H U ) = A ) )

  proof
    cR
    crngo
    wcel
    #
    cA
    cX
    wcel
    #
    cU
    cA
    cH
    co
    cA
    wceq
    cA
    cU
    cH
    co
    cA
    wceq
    wa
    #
    @0
    @1
    @2
    wi
    #
    cA
    cH
    crn
    #
    wcel
    #
    @2
    wi
    #
    @0
    cH
    cmndo
    wcel
    cH
    cmagm
    cexid
    cin
    wcel
    #
    @6
    cR
    cH
    uridm.1
    rngomndo
    cH
    mndomgmid
    @7
    @5
    @2
    cA
    cU
    cH
    @4
    @4
    eqid
    uridm.3
    cmpidelt
    ex
    3syl
    cR
    c1st
    cfv
    #
    crn
    #
    @4
    wceq
    #
    @0
    @3
    @6
    wb
    #
    cR
    @8
    cH
    uridm.1
    @8
    eqid
    rngorn1eq
    cX
    @9
    wceq
    #
    @10
    @0
    @11
    wi
    #
    uridm.2
    @12
    @10
    wa
    cX
    @4
    wceq
    #
    @13
    cX
    @9
    @4
    eqtr
    @14
    @0
    @11
    @14
    @0
    wa
    #
    @1
    @5
    @2
    @15
    cX
    @4
    cA
    @14
    @0
    simpl
    eleq2d
    imbi1d
    ex
    syl
    mpan
    mpcom
    mpbird
    imp
end
