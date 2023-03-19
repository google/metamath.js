include "crngo.mm"
include "wcel.mm"
include "cidl.mm"
include "cfv.mm"
include "wa.mm"
include "wss.mm"
include "cgi.mm"
include "cv.mm"
include "co.mm"
include "wral.mm"
include "c2nd.mm"
include "w3a.mm"
include "eqid.mm"
include "isidl.mm"
include "biimpa.mm"
include "simp1d.mm"

theorem idlss
  let cR: class R
  let cG: class G
  let cI: class I
  let cX: class X
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume idlss.1: |- G = ( 1st ` R )
  assume idlss.2: |- X = ran G


  assert |- ( ( R e. RingOps /\ I e. ( Idl ` R ) ) -> I C_ X )

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
    cI
    cX
    wss
    #
    cG
    cgi
    cfv
    #
    cI
    wcel
    #
    vx
    cv
    #
    vy
    cv
    cG
    co
    cI
    wcel
    vy
    cI
    wral
    vz
    cv
    #
    @5
    cR
    c2nd
    cfv
    #
    co
    cI
    wcel
    @5
    @6
    @7
    co
    cI
    wcel
    wa
    vz
    cX
    wral
    wa
    vx
    cI
    wral
    #
    @0
    @1
    @2
    @4
    @8
    w3a
    vx
    vy
    vz
    cR
    cG
    @7
    cI
    cX
    @3
    idlss.1
    @7
    eqid
    idlss.2
    @3
    eqid
    isidl
    biimpa
    simp1d
end
