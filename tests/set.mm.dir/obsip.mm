include "cobs.mm"
include "cfv.mm"
include "wcel.mm"
include "co.mm"
include "wceq.mm"
include "cif.mm"
include "cv.mm"
include "wral.mm"
include "wa.mm"
include "cocv.mm"
include "c0g.mm"
include "csn.mm"
include "cphl.mm"
include "wss.mm"
include "eqid.mm"
include "isobs.mm"
include "simp3bi.mm"
include "simpld.mm"
include "oveq1.mm"
include "eqeq1.mm"
include "ifbid.mm"
include "eqeq12d.mm"
include "oveq2.mm"
include "eqeq2.mm"
include "rspc2v.mm"
include "syl5com.mm"
include "3impib.mm"

theorem obsip
  let cB: class B
  let cP: class P
  let cQ: class Q
  let c.1: class .1.
  let cF: class F
  let c.xi: class .,
  let cV: class V
  let cW: class W
  let c.0: class .0.
  let vb: setvar b
  let vh: setvar h
  let vx: setvar x
  let vy: setvar y
  let c.pe: class ._|_
  let cY: class Y
  assume isobs.v: |- V = ( Base ` W )
  assume isobs.h: |- ., = ( .i ` W )
  assume isobs.f: |- F = ( Scalar ` W )
  assume isobs.u: |- .1. = ( 1r ` F )
  assume isobs.z: |- .0. = ( 0g ` F )


  assert |- ( ( B e. ( OBasis ` W ) /\ P e. B /\ Q e. B ) -> ( P ., Q ) = if ( P = Q , .1. , .0. ) )

  proof
    cB
    cW
    cobs
    cfv
    wcel
    #
    cP
    cB
    wcel
    #
    cQ
    cB
    wcel
    #
    cP
    cQ
    c.xi
    co
    #
    cP
    cQ
    wceq
    #
    c.1
    c.0
    cif
    #
    wceq
    #
    @0
    vx
    cv
    #
    vy
    cv
    #
    c.xi
    co
    #
    @7
    @8
    wceq
    #
    c.1
    c.0
    cif
    #
    wceq
    #
    vy
    cB
    wral
    vx
    cB
    wral
    #
    @1
    @2
    wa
    @6
    @0
    @13
    cB
    cW
    cocv
    cfv
    #
    cfv
    cW
    c0g
    cfv
    #
    csn
    wceq
    #
    @0
    cW
    cphl
    wcel
    cB
    cV
    wss
    @13
    @16
    wa
    vx
    vy
    cB
    c.1
    cF
    c.xi
    @14
    cV
    cW
    @15
    c.0
    isobs.v
    isobs.h
    isobs.f
    isobs.u
    isobs.z
    @14
    eqid
    @15
    eqid
    isobs
    simp3bi
    simpld
    @12
    @6
    cP
    @8
    c.xi
    co
    #
    cP
    @8
    wceq
    #
    c.1
    c.0
    cif
    #
    wceq
    vx
    vy
    cP
    cQ
    cB
    cB
    @7
    cP
    wceq
    #
    @9
    @17
    @11
    @19
    @7
    cP
    @8
    c.xi
    oveq1
    @20
    @10
    @18
    c.1
    c.0
    @7
    cP
    @8
    eqeq1
    ifbid
    eqeq12d
    @8
    cQ
    wceq
    #
    @17
    @3
    @19
    @5
    @8
    cQ
    cP
    c.xi
    oveq2
    @21
    @18
    @4
    c.1
    c.0
    @8
    cQ
    cP
    eqeq2
    ifbid
    eqeq12d
    rspc2v
    syl5com
    3impib
end
