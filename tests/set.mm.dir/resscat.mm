include "ccat.mm"
include "wcel.mm"
include "wa.mm"
include "cress.mm"
include "co.mm"
include "cbs.mm"
include "cfv.mm"
include "cin.mm"
include "wceq.mm"
include "eqid.mm"
include "ressinbas.mm"
include "adantl.mm"
include "chomf.mm"
include "cxp.mm"
include "cres.mm"
include "cresc.mm"
include "simpl.mm"
include "wss.mm"
include "inss2.mm"
include "a1i.mm"
include "fullsubc.mm"
include "subccat.mm"
include "cvv.mm"
include "ccomf.mm"
include "fullresc.mm"
include "simpld.mm"
include "simprd.mm"
include "ovexd.mm"
include "catpropd.mm"
include "mpbird.mm"
include "eqeltrd.mm"

theorem resscat
  let cC: class C
  let cS: class S
  let cV: class V


  assert |- ( ( C e. Cat /\ S e. V ) -> ( C |`s S ) e. Cat )

  proof
    cC
    ccat
    wcel
    #
    cS
    cV
    wcel
    #
    wa
    #
    cC
    cS
    cress
    co
    #
    cC
    cS
    cC
    cbs
    cfv
    #
    cin
    #
    cress
    co
    #
    ccat
    @1
    @3
    @6
    wceq
    @0
    cS
    @4
    cC
    cV
    @4
    eqid
    #
    ressinbas
    adantl
    @2
    @6
    ccat
    wcel
    cC
    cC
    chomf
    cfv
    #
    @5
    @5
    cxp
    cres
    #
    cresc
    co
    #
    ccat
    wcel
    @2
    cC
    @10
    @9
    @10
    eqid
    #
    @2
    @4
    cC
    @5
    @8
    @7
    @8
    eqid
    #
    @0
    @1
    simpl
    #
    @5
    @4
    wss
    @2
    cS
    @4
    inss2
    a1i
    #
    fullsubc
    subccat
    #
    @2
    @6
    @10
    cvv
    ccat
    @2
    @6
    chomf
    cfv
    @10
    chomf
    cfv
    wceq
    #
    @6
    ccomf
    cfv
    @10
    ccomf
    cfv
    wceq
    #
    @2
    @4
    cC
    @6
    @5
    @10
    @8
    @7
    @12
    @13
    @14
    @6
    eqid
    @11
    fullresc
    #
    simpld
    @2
    @16
    @17
    @18
    simprd
    @2
    cC
    @5
    cress
    ovexd
    @15
    catpropd
    mpbird
    eqeltrd
end
