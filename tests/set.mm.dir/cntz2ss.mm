include "wss.mm"
include "wa.mm"
include "cfv.mm"
include "cv.mm"
include "cplusg.mm"
include "co.mm"
include "wceq.mm"
include "wral.mm"
include "wcel.mm"
include "eqid.mm"
include "cntzi.mm"
include "ralrimiva.mm"
include "wi.mm"
include "ssralv.mm"
include "adantl.mm"
include "syl5.mm"
include "ralrimiv.mm"
include "wb.mm"
include "cntzssv.mm"
include "sstr.mm"
include "ancoms.mm"
include "sscntz.mm"
include "sylancr.mm"
include "mpbird.mm"

theorem cntz2ss
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


  assert |- ( ( S C_ B /\ T C_ S ) -> ( Z ` S ) C_ ( Z ` T ) )

  proof
    cS
    cB
    wss
    #
    cT
    cS
    wss
    #
    wa
    #
    cS
    cZ
    cfv
    #
    cT
    cZ
    cfv
    wss
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
    @6
    @5
    @7
    co
    wceq
    #
    vy
    cT
    wral
    #
    vx
    @3
    wral
    #
    @2
    @9
    vx
    @3
    @5
    @3
    wcel
    #
    @8
    vy
    cS
    wral
    #
    @2
    @9
    @11
    @8
    vy
    cS
    @7
    cS
    cM
    @5
    @6
    cZ
    @7
    eqid
    #
    cntzrec.z
    cntzi
    ralrimiva
    @1
    @12
    @9
    wi
    @0
    @8
    vy
    cT
    cS
    ssralv
    adantl
    syl5
    ralrimiv
    @2
    @3
    cB
    wss
    cT
    cB
    wss
    #
    @4
    @10
    wb
    cB
    cS
    cM
    cZ
    cntzrec.b
    cntzrec.z
    cntzssv
    @1
    @0
    @14
    cT
    cS
    cB
    sstr
    ancoms
    vx
    vy
    cB
    @7
    @3
    cT
    cM
    cZ
    cntzrec.b
    @13
    cntzrec.z
    sscntz
    sylancr
    mpbird
end
