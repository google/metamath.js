include "wcel.mm"
include "wss.mm"
include "co.mm"
include "cv.mm"
include "cmpt2.mm"
include "crn.mm"
include "wceq.mm"
include "wa.mm"
include "cpw.mm"
include "lsmfval.mm"
include "oveqd.mm"
include "cbs.mm"
include "cfv.mm"
include "cvv.mm"
include "fvex.mm"
include "eqeltri.mm"
include "elpw2.mm"
include "mpt2exga.mm"
include "rnexg.mm"
include "syl.mm"
include "mpt2eq12.mm"
include "rneqd.mm"
include "eqid.mm"
include "ovmpt2ga.mm"
include "mpd3an3.mm"
include "syl2anbr.mm"
include "sylan9eq.mm"
include "3impb.mm"

theorem lsmvalx
  let vx: setvar x
  let vy: setvar y
  let cB: class B
  let c.pl: class .+
  let c.po: class .(+)
  let cT: class T
  let cU: class U
  let cG: class G
  let cV: class V
  let vt: setvar t
  let vu: setvar u
  let vw: setvar w
  let vz: setvar z
  let cX: class X
  let cY: class Y
  assume lsmfval.v: |- B = ( Base ` G )
  assume lsmfval.a: |- .+ = ( +g ` G )
  assume lsmfval.s: |- .(+) = ( LSSum ` G )

  disjoint x y
  disjoint .+ x
  disjoint .+ y
  disjoint B x
  disjoint B y
  disjoint T x
  disjoint T y
  disjoint G x
  disjoint G y
  disjoint U x
  disjoint U y
  disjoint t u
  disjoint t w
  disjoint t x
  disjoint t y
  disjoint t z
  disjoint .+ t
  disjoint u w
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint .+ u
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint .+ w
  disjoint x z
  disjoint y z
  disjoint .+ z
  disjoint B t
  disjoint B u
  disjoint B w
  disjoint B z
  disjoint T t
  disjoint T u
  disjoint T z
  disjoint X x
  disjoint X y
  disjoint X z
  disjoint G t
  disjoint G u
  disjoint G w
  disjoint G z
  disjoint U t
  disjoint U u
  disjoint U z
  disjoint Y x
  disjoint Y y
  assert |- ( ( G e. V /\ T C_ B /\ U C_ B ) -> ( T .(+) U ) = ran ( x e. T , y e. U |-> ( x .+ y ) ) )

  proof
    cG
    cV
    wcel
    #
    cT
    cB
    wss
    #
    cU
    cB
    wss
    #
    cT
    cU
    c.po
    co
    #
    vx
    vy
    cT
    cU
    vx
    cv
    vy
    cv
    c.pl
    co
    #
    cmpt2
    #
    crn
    #
    wceq
    @0
    @1
    @2
    wa
    @3
    cT
    cU
    vt
    vu
    cB
    cpw
    #
    @7
    vx
    vy
    vt
    cv
    #
    vu
    cv
    #
    @4
    cmpt2
    #
    crn
    #
    cmpt2
    #
    co
    #
    @6
    @0
    c.po
    @12
    cT
    cU
    vx
    vy
    vu
    vt
    cB
    c.pl
    c.po
    cG
    cV
    lsmfval.v
    lsmfval.a
    lsmfval.s
    lsmfval
    oveqd
    @1
    cT
    @7
    wcel
    #
    cU
    @7
    wcel
    #
    @13
    @6
    wceq
    #
    @2
    cT
    cB
    cB
    cG
    cbs
    cfv
    cvv
    lsmfval.v
    cG
    cbs
    fvex
    eqeltri
    #
    elpw2
    cU
    cB
    @17
    elpw2
    @14
    @15
    @6
    cvv
    wcel
    #
    @16
    @14
    @15
    wa
    @5
    cvv
    wcel
    @18
    vx
    vy
    cT
    cU
    @4
    @7
    @7
    mpt2exga
    @5
    cvv
    rnexg
    syl
    vt
    vu
    cT
    cU
    @7
    @7
    @11
    @6
    @12
    cvv
    @8
    cT
    wceq
    @9
    cU
    wceq
    wa
    @10
    @5
    vx
    vy
    @8
    @9
    cT
    cU
    @4
    mpt2eq12
    rneqd
    @12
    eqid
    ovmpt2ga
    mpd3an3
    syl2anbr
    sylan9eq
    3impb
end
