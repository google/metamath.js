include "crngo.mm"
include "wcel.mm"
include "cidl.mm"
include "cfv.mm"
include "wss.mm"
include "cgi.mm"
include "cv.mm"
include "co.mm"
include "wral.mm"
include "c2nd.mm"
include "wa.mm"
include "ssid.mm"
include "a1i.mm"
include "eqid.mm"
include "rngo0cl.mm"
include "rngogcl.mm"
include "3expa.mm"
include "ralrimiva.mm"
include "w3a.mm"
include "rngocl.mm"
include "3com23.mm"
include "jca.mm"
include "isidl.mm"
include "mpbir3and.mm"

theorem rngoidl
  let cR: class R
  let cG: class G
  let cX: class X
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume rngidl.1: |- G = ( 1st ` R )
  assume rngidl.2: |- X = ran G


  assert |- ( R e. RingOps -> X e. ( Idl ` R ) )

  proof
    cR
    crngo
    wcel
    #
    cX
    cR
    cidl
    cfv
    wcel
    cX
    cX
    wss
    #
    cG
    cgi
    cfv
    #
    cX
    wcel
    vx
    cv
    #
    vy
    cv
    #
    cG
    co
    cX
    wcel
    #
    vy
    cX
    wral
    #
    vz
    cv
    #
    @3
    cR
    c2nd
    cfv
    #
    co
    cX
    wcel
    #
    @3
    @7
    @8
    co
    cX
    wcel
    #
    wa
    #
    vz
    cX
    wral
    #
    wa
    #
    vx
    cX
    wral
    @1
    @0
    cX
    ssid
    a1i
    cR
    cG
    cX
    @2
    rngidl.1
    rngidl.2
    @2
    eqid
    #
    rngo0cl
    @0
    @13
    vx
    cX
    @0
    @3
    cX
    wcel
    #
    wa
    #
    @6
    @12
    @16
    @5
    vy
    cX
    @0
    @15
    @4
    cX
    wcel
    @5
    @3
    @4
    cR
    cG
    cX
    rngidl.1
    rngidl.2
    rngogcl
    3expa
    ralrimiva
    @16
    @11
    vz
    cX
    @0
    @15
    @7
    cX
    wcel
    #
    @11
    @0
    @15
    @17
    w3a
    @9
    @10
    @0
    @17
    @15
    @9
    @7
    @3
    cR
    cG
    @8
    cX
    rngidl.1
    @8
    eqid
    #
    rngidl.2
    rngocl
    3com23
    @3
    @7
    cR
    cG
    @8
    cX
    rngidl.1
    @18
    rngidl.2
    rngocl
    jca
    3expa
    ralrimiva
    jca
    ralrimiva
    vx
    vy
    vz
    cR
    cG
    @8
    cX
    cX
    @2
    rngidl.1
    @18
    rngidl.2
    @14
    isidl
    mpbir3and
end
