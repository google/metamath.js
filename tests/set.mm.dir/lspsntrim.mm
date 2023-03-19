include "clmod.mm"
include "wcel.mm"
include "w3a.mm"
include "cminusg.mm"
include "cfv.mm"
include "cplusg.mm"
include "co.mm"
include "csn.mm"
include "wss.mm"
include "eqid.mm"
include "lmodvnegcl.mm"
include "3adant2.mm"
include "lspsntri.mm"
include "syld3an3.mm"
include "wceq.mm"
include "wa.mm"
include "grpsubval.mm"
include "sneqd.mm"
include "fveq2d.mm"
include "3adant1.mm"
include "lspsnneg.mm"
include "eqcomd.mm"
include "oveq2d.mm"
include "3sstr4d.mm"

theorem lspsntrim
  let c.po: class .(+)
  let c.mi: class .-
  let cN: class N
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  assume lspsntrim.v: |- V = ( Base ` W )
  assume lspsntrim.s: |- .- = ( -g ` W )
  assume lspsntrim.p: |- .(+) = ( LSSum ` W )
  assume lspsntrim.n: |- N = ( LSpan ` W )


  assert |- ( ( W e. LMod /\ X e. V /\ Y e. V ) -> ( N ` { ( X .- Y ) } ) C_ ( ( N ` { X } ) .(+) ( N ` { Y } ) ) )

  proof
    cW
    clmod
    wcel
    #
    cX
    cV
    wcel
    #
    cY
    cV
    wcel
    #
    w3a
    #
    cX
    cY
    cW
    cminusg
    cfv
    #
    cfv
    #
    cW
    cplusg
    cfv
    #
    co
    #
    csn
    #
    cN
    cfv
    #
    cX
    csn
    cN
    cfv
    #
    @5
    csn
    cN
    cfv
    #
    c.po
    co
    #
    cX
    cY
    c.mi
    co
    #
    csn
    #
    cN
    cfv
    #
    @10
    cY
    csn
    cN
    cfv
    #
    c.po
    co
    @0
    @1
    @2
    @5
    cV
    wcel
    #
    @9
    @12
    wss
    @0
    @2
    @17
    @1
    @4
    cV
    cW
    cY
    lspsntrim.v
    @4
    eqid
    #
    lmodvnegcl
    3adant2
    @6
    c.po
    cN
    cV
    cW
    cX
    @5
    lspsntrim.v
    @6
    eqid
    #
    lspsntrim.n
    lspsntrim.p
    lspsntri
    syld3an3
    @1
    @2
    @15
    @9
    wceq
    @0
    @1
    @2
    wa
    #
    @14
    @8
    cN
    @20
    @13
    @7
    cV
    @6
    cW
    @4
    c.mi
    cX
    cY
    lspsntrim.v
    @19
    @18
    lspsntrim.s
    grpsubval
    sneqd
    fveq2d
    3adant1
    @3
    @16
    @11
    @10
    c.po
    @3
    @11
    @16
    @0
    @2
    @11
    @16
    wceq
    @1
    @4
    cN
    cV
    cW
    cY
    lspsntrim.v
    @18
    lspsntrim.n
    lspsnneg
    3adant2
    eqcomd
    oveq2d
    3sstr4d
end
