include "cnv.mm"
include "wcel.mm"
include "wa.mm"
include "co.mm"
include "ccj.mm"
include "cfv.mm"
include "cc0.mm"
include "wceq.mm"
include "nvzcl.mm"
include "adantr.mm"
include "dipcj.mm"
include "mpd3an3.mm"
include "dip0r.mm"
include "fveq2d.mm"
include "cj0.mm"
include "syl6eq.mm"
include "eqtr3d.mm"

theorem dip0l
  let cA: class A
  let cP: class P
  let cU: class U
  let cX: class X
  let cZ: class Z
  assume dip0r.1: |- X = ( BaseSet ` U )
  assume dip0r.5: |- Z = ( 0vec ` U )
  assume dip0r.7: |- P = ( .iOLD ` U )


  assert |- ( ( U e. NrmCVec /\ A e. X ) -> ( Z P A ) = 0 )

  proof
    cU
    cnv
    wcel
    #
    cA
    cX
    wcel
    #
    wa
    #
    cA
    cZ
    cP
    co
    #
    ccj
    cfv
    #
    cZ
    cA
    cP
    co
    #
    cc0
    @0
    @1
    cZ
    cX
    wcel
    #
    @4
    @5
    wceq
    @0
    @6
    @1
    cU
    cX
    cZ
    dip0r.1
    dip0r.5
    nvzcl
    adantr
    cA
    cZ
    cP
    cU
    cX
    dip0r.1
    dip0r.7
    dipcj
    mpd3an3
    @2
    @4
    cc0
    ccj
    cfv
    cc0
    @2
    @3
    cc0
    ccj
    cA
    cP
    cU
    cX
    cZ
    dip0r.1
    dip0r.5
    dip0r.7
    dip0r
    fveq2d
    cj0
    syl6eq
    eqtr3d
end
