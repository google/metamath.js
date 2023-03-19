include "csubg.mm"
include "cfv.mm"
include "wcel.mm"
include "w3a.mm"
include "cminusg.mm"
include "cplusg.mm"
include "co.mm"
include "wceq.mm"
include "eqid.mm"
include "ressplusg.mm"
include "3ad2ant1.mm"
include "eqidd.mm"
include "subginv.mm"
include "3adant2.mm"
include "oveq123d.mm"
include "cbs.mm"
include "wss.mm"
include "subgss.mm"
include "simp2.mm"
include "sseldd.mm"
include "simp3.mm"
include "grpsubval.mm"
include "syl2anc.mm"
include "subgbas.mm"
include "eleqtrd.mm"
include "3eqtr4d.mm"

theorem subgsub
  let cS: class S
  let cG: class G
  let cH: class H
  let c.mi: class .-
  let cN: class N
  let cX: class X
  let cY: class Y
  assume subgsubcl.p: |- .- = ( -g ` G )
  assume subgsub.h: |- H = ( G |`s S )
  assume subgsub.n: |- N = ( -g ` H )


  assert |- ( ( S e. ( SubGrp ` G ) /\ X e. S /\ Y e. S ) -> ( X .- Y ) = ( X N Y ) )

  proof
    cS
    cG
    csubg
    cfv
    #
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
    cX
    cY
    cH
    cminusg
    cfv
    #
    cfv
    #
    cH
    cplusg
    cfv
    #
    co
    #
    cX
    cY
    c.mi
    co
    #
    cX
    cY
    cN
    co
    #
    @4
    cX
    cX
    @6
    @10
    @7
    @11
    @1
    @2
    @7
    @11
    wceq
    @3
    cS
    @7
    cG
    cH
    @0
    subgsub.h
    @7
    eqid
    #
    ressplusg
    3ad2ant1
    @4
    cX
    eqidd
    @1
    @3
    @6
    @10
    wceq
    @2
    cS
    cG
    cH
    @5
    @9
    cY
    subgsub.h
    @5
    eqid
    #
    @9
    eqid
    #
    subginv
    3adant2
    oveq123d
    @4
    cX
    cG
    cbs
    cfv
    #
    wcel
    cY
    @18
    wcel
    @13
    @8
    wceq
    @4
    cS
    @18
    cX
    @1
    @2
    cS
    @18
    wss
    @3
    @18
    cS
    cG
    @18
    eqid
    #
    subgss
    3ad2ant1
    #
    @1
    @2
    @3
    simp2
    #
    sseldd
    @4
    cS
    @18
    cY
    @20
    @1
    @2
    @3
    simp3
    #
    sseldd
    @18
    @7
    cG
    @5
    c.mi
    cX
    cY
    @19
    @15
    @16
    subgsubcl.p
    grpsubval
    syl2anc
    @4
    cX
    cH
    cbs
    cfv
    #
    wcel
    cY
    @23
    wcel
    @14
    @12
    wceq
    @4
    cX
    cS
    @23
    @21
    @1
    @2
    cS
    @23
    wceq
    @3
    cS
    cG
    cH
    subgsub.h
    subgbas
    3ad2ant1
    #
    eleqtrd
    @4
    cY
    cS
    @23
    @22
    @24
    eleqtrd
    @23
    @11
    cH
    @9
    cN
    cX
    cY
    @23
    eqid
    @11
    eqid
    @17
    subgsub.n
    grpsubval
    syl2anc
    3eqtr4d
end
