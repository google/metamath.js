include "wss.mm"
include "wa.mm"
include "cv.mm"
include "cplusg.mm"
include "cfv.mm"
include "co.mm"
include "wceq.mm"
include "wral.mm"
include "wb.mm"
include "ralcom.mm"
include "eqcom.mm"
include "2ralbii.mm"
include "bitri.mm"
include "a1i.mm"
include "eqid.mm"
include "sscntz.mm"
include "ancoms.mm"
include "3bitr4d.mm"

theorem cntzrec
  let cB: class B
  let cS: class S
  let cT: class T
  let cM: class M
  let cZ: class Z
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume cntzrec.b: |- B = ( Base ` M )
  assume cntzrec.z: |- Z = ( Cntz ` M )


  assert |- ( ( S C_ B /\ T C_ B ) -> ( S C_ ( Z ` T ) <-> T C_ ( Z ` S ) ) )

  proof
    cS
    cB
    wss
    #
    cT
    cB
    wss
    #
    wa
    #
    vx
    cv
    #
    vy
    cv
    #
    cM
    cplusg
    cfv
    #
    co
    #
    @4
    @3
    @5
    co
    #
    wceq
    #
    vy
    cT
    wral
    vx
    cS
    wral
    #
    @7
    @6
    wceq
    #
    vx
    cS
    wral
    vy
    cT
    wral
    #
    cS
    cT
    cZ
    cfv
    wss
    cT
    cS
    cZ
    cfv
    wss
    #
    @9
    @11
    wb
    @2
    @9
    @8
    vx
    cS
    wral
    vy
    cT
    wral
    @11
    @8
    vx
    vy
    cS
    cT
    ralcom
    @8
    @10
    vy
    vx
    cT
    cS
    @6
    @7
    eqcom
    2ralbii
    bitri
    a1i
    vx
    vy
    cB
    @5
    cS
    cT
    cM
    cZ
    cntzrec.b
    @5
    eqid
    #
    cntzrec.z
    sscntz
    @1
    @0
    @12
    @11
    wb
    vy
    vx
    cB
    @5
    cT
    cS
    cM
    cZ
    cntzrec.b
    @13
    cntzrec.z
    sscntz
    ancoms
    3bitr4d
end
