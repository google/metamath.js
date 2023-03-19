include "csubg.mm"
include "cfv.mm"
include "wcel.mm"
include "w3a.mm"
include "co.mm"
include "cminusg.mm"
include "cplusg.mm"
include "cbs.mm"
include "wceq.mm"
include "wss.mm"
include "eqid.mm"
include "subgss.mm"
include "3ad2ant1.mm"
include "simp2.mm"
include "sseldd.mm"
include "simp3.mm"
include "grpsubval.mm"
include "syl2anc.mm"
include "subginvcl.mm"
include "3adant2.mm"
include "subgcl.mm"
include "syld3an3.mm"
include "eqeltrd.mm"

theorem subgsubcl
  let cS: class S
  let cG: class G
  let c.mi: class .-
  let cX: class X
  let cY: class Y
  assume subgsubcl.p: |- .- = ( -g ` G )


  assert |- ( ( S e. ( SubGrp ` G ) /\ X e. S /\ Y e. S ) -> ( X .- Y ) e. S )

  proof
    cS
    cG
    csubg
    cfv
    wcel
    #
    cX
    cS
    wcel
    #
    cY
    cS
    wcel
    #
    w3a
    #
    cX
    cY
    c.mi
    co
    #
    cX
    cY
    cG
    cminusg
    cfv
    #
    cfv
    #
    cG
    cplusg
    cfv
    #
    co
    #
    cS
    @3
    cX
    cG
    cbs
    cfv
    #
    wcel
    cY
    @9
    wcel
    @4
    @8
    wceq
    @3
    cS
    @9
    cX
    @0
    @1
    cS
    @9
    wss
    @2
    @9
    cS
    cG
    @9
    eqid
    #
    subgss
    3ad2ant1
    #
    @0
    @1
    @2
    simp2
    sseldd
    @3
    cS
    @9
    cY
    @11
    @0
    @1
    @2
    simp3
    sseldd
    @9
    @7
    cG
    @5
    c.mi
    cX
    cY
    @10
    @7
    eqid
    #
    @5
    eqid
    #
    subgsubcl.p
    grpsubval
    syl2anc
    @0
    @1
    @2
    @6
    cS
    wcel
    #
    @8
    cS
    wcel
    @0
    @2
    @14
    @1
    cS
    cG
    @5
    cY
    @13
    subginvcl
    3adant2
    @7
    cS
    cG
    cX
    @6
    @12
    subgcl
    syld3an3
    eqeltrd
end
