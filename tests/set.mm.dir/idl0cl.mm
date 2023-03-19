include "crngo.mm"
include "wcel.mm"
include "cidl.mm"
include "cfv.mm"
include "wa.mm"
include "crn.mm"
include "wss.mm"
include "cv.mm"
include "co.mm"
include "wral.mm"
include "c2nd.mm"
include "w3a.mm"
include "eqid.mm"
include "isidl.mm"
include "biimpa.mm"
include "simp2d.mm"

theorem idl0cl
  let cR: class R
  let cG: class G
  let cI: class I
  let cZ: class Z
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume idl0cl.1: |- G = ( 1st ` R )
  assume idl0cl.2: |- Z = ( GId ` G )


  assert |- ( ( R e. RingOps /\ I e. ( Idl ` R ) ) -> Z e. I )

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
    cG
    crn
    #
    wss
    #
    cZ
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
    @2
    wral
    wa
    vx
    cI
    wral
    #
    @0
    @1
    @3
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
    @2
    cZ
    idl0cl.1
    @7
    eqid
    @2
    eqid
    idl0cl.2
    isidl
    biimpa
    simp2d
end
