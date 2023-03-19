include "cfld.mm"
include "wcel.mm"
include "ccring.mm"
include "cgi.mm"
include "cfv.mm"
include "wne.mm"
include "cidl.mm"
include "csn.mm"
include "cpr.mm"
include "wceq.mm"
include "w3a.mm"
include "eqid.mm"
include "isfldidl.mm"
include "wa.mm"
include "crngo.mm"
include "wb.mm"
include "crngorngo.mm"
include "eqcom.mm"
include "0rngo.mm"
include "syl5bb.mm"
include "syl.mm"
include "necon3bid.mm"
include "anbi1d.mm"
include "pm5.32i.mm"
include "3anass.mm"
include "3bitr4i.mm"
include "bitri.mm"

theorem isfldidl2
  let cG: class G
  let cH: class H
  let cK: class K
  let cX: class X
  let cZ: class Z
  assume isfldidl2.1: |- G = ( 1st ` K )
  assume isfldidl2.2: |- H = ( 2nd ` K )
  assume isfldidl2.3: |- X = ran G
  assume isfldidl2.4: |- Z = ( GId ` G )


  assert |- ( K e. Fld <-> ( K e. CRingOps /\ X =/= { Z } /\ ( Idl ` K ) = { { Z } , X } ) )

  proof
    cK
    cfld
    wcel
    cK
    ccring
    wcel
    #
    cH
    cgi
    cfv
    #
    cZ
    wne
    #
    cK
    cidl
    cfv
    cZ
    csn
    #
    cX
    cpr
    wceq
    #
    w3a
    #
    @0
    cX
    @3
    wne
    #
    @4
    w3a
    #
    @1
    cG
    cH
    cK
    cX
    cZ
    isfldidl2.1
    isfldidl2.2
    isfldidl2.3
    isfldidl2.4
    @1
    eqid
    #
    isfldidl
    @0
    @2
    @4
    wa
    #
    wa
    @0
    @6
    @4
    wa
    #
    wa
    @5
    @7
    @0
    @9
    @10
    @0
    @2
    @6
    @4
    @0
    @1
    cZ
    cX
    @3
    @0
    cK
    crngo
    wcel
    #
    @1
    cZ
    wceq
    #
    cX
    @3
    wceq
    #
    wb
    cK
    crngorngo
    @12
    cZ
    @1
    wceq
    @11
    @13
    @1
    cZ
    eqcom
    cK
    @1
    cG
    cH
    cX
    cZ
    isfldidl2.1
    isfldidl2.2
    isfldidl2.3
    isfldidl2.4
    @8
    0rngo
    syl5bb
    syl
    necon3bid
    anbi1d
    pm5.32i
    @0
    @2
    @4
    3anass
    @0
    @6
    @4
    3anass
    3bitr4i
    bitri
end
