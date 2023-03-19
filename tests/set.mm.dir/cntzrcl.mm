include "cfv.mm"
include "wcel.mm"
include "cvv.mm"
include "wss.mm"
include "wn.mm"
include "c0.mm"
include "noel.mm"
include "ccntz.mm"
include "fvprc.mm"
include "syl5eq.mm"
include "fveq1d.mm"
include "0fv.mm"
include "syl6eq.mm"
include "eleq2d.mm"
include "mtbiri.mm"
include "con4i.mm"
include "cdm.mm"
include "cpw.mm"
include "cv.mm"
include "cplusg.mm"
include "co.mm"
include "wceq.mm"
include "wral.mm"
include "crab.mm"
include "cmpt.mm"
include "eqid.mm"
include "cntzfval.mm"
include "syl.mm"
include "dmeqd.mm"
include "dmmptss.mm"
include "syl6eqss.mm"
include "elfvdm.mm"
include "sseldd.mm"
include "elpwid.mm"
include "jca.mm"

theorem cntzrcl
  let cB: class B
  let cS: class S
  let cM: class M
  let cX: class X
  let cZ: class Z
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume cntzrcl.b: |- B = ( Base ` M )
  assume cntzrcl.z: |- Z = ( Cntz ` M )


  assert |- ( X e. ( Z ` S ) -> ( M e. _V /\ S C_ B ) )

  proof
    cX
    cS
    cZ
    cfv
    #
    wcel
    #
    cM
    cvv
    wcel
    #
    cS
    cB
    wss
    @2
    @1
    @2
    wn
    #
    @1
    cX
    c0
    wcel
    cX
    noel
    @3
    @0
    c0
    cX
    @3
    @0
    cS
    c0
    cfv
    c0
    @3
    cS
    cZ
    c0
    @3
    cZ
    cM
    ccntz
    cfv
    c0
    cntzrcl.z
    cM
    ccntz
    fvprc
    syl5eq
    fveq1d
    cS
    0fv
    syl6eq
    eleq2d
    mtbiri
    con4i
    #
    @1
    cS
    cB
    @1
    cZ
    cdm
    #
    cB
    cpw
    #
    cS
    @1
    @5
    vx
    @6
    vy
    cv
    #
    vz
    cv
    #
    cM
    cplusg
    cfv
    #
    co
    @8
    @7
    @9
    co
    wceq
    vz
    vx
    cv
    wral
    vy
    cB
    crab
    #
    cmpt
    #
    cdm
    @6
    @1
    cZ
    @11
    @1
    @2
    cZ
    @11
    wceq
    @4
    vy
    vz
    cB
    @9
    cM
    cvv
    cZ
    vx
    cntzrcl.b
    @9
    eqid
    cntzrcl.z
    cntzfval
    syl
    dmeqd
    vx
    @6
    @10
    @11
    @11
    eqid
    dmmptss
    syl6eqss
    cX
    cS
    cZ
    elfvdm
    sseldd
    elpwid
    jca
end
