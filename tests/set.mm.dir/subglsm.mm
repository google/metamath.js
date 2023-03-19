include "csubg.mm"
include "cfv.mm"
include "wcel.mm"
include "wss.mm"
include "w3a.mm"
include "cv.mm"
include "cplusg.mm"
include "co.mm"
include "cmpt2.mm"
include "crn.mm"
include "wceq.mm"
include "simp11.mm"
include "eqid.mm"
include "ressplusg.mm"
include "syl.mm"
include "oveqd.mm"
include "mpt2eq3dva.mm"
include "rneqd.mm"
include "cgrp.mm"
include "cbs.mm"
include "subgrcl.mm"
include "3ad2ant1.mm"
include "simp2.mm"
include "subgss.mm"
include "sstrd.mm"
include "simp3.mm"
include "lsmvalx.mm"
include "syl3anc.mm"
include "subggrp.mm"
include "subgbas.mm"
include "sseqtrd.mm"
include "3eqtr4d.mm"

theorem subglsm
  let cA: class A
  let c.po: class .(+)
  let cS: class S
  let cT: class T
  let cU: class U
  let cG: class G
  let cH: class H
  let vx: setvar x
  let vy: setvar y
  assume subglsm.h: |- H = ( G |`s S )
  assume subglsm.s: |- .(+) = ( LSSum ` G )
  assume subglsm.a: |- A = ( LSSum ` H )


  assert |- ( ( S e. ( SubGrp ` G ) /\ T C_ S /\ U C_ S ) -> ( T .(+) U ) = ( T A U ) )

  proof
    cS
    cG
    csubg
    cfv
    #
    wcel
    #
    cT
    cS
    wss
    #
    cU
    cS
    wss
    #
    w3a
    #
    vx
    vy
    cT
    cU
    vx
    cv
    #
    vy
    cv
    #
    cG
    cplusg
    cfv
    #
    co
    #
    cmpt2
    #
    crn
    #
    vx
    vy
    cT
    cU
    @5
    @6
    cH
    cplusg
    cfv
    #
    co
    #
    cmpt2
    #
    crn
    #
    cT
    cU
    c.po
    co
    #
    cT
    cU
    cA
    co
    #
    @4
    @9
    @13
    @4
    vx
    vy
    cT
    cU
    @8
    @12
    @4
    @5
    cT
    wcel
    #
    @6
    cU
    wcel
    #
    w3a
    #
    @7
    @11
    @5
    @6
    @19
    @1
    @7
    @11
    wceq
    @1
    @2
    @3
    @17
    @18
    simp11
    cS
    @7
    cG
    cH
    @0
    subglsm.h
    @7
    eqid
    #
    ressplusg
    syl
    oveqd
    mpt2eq3dva
    rneqd
    @4
    cG
    cgrp
    wcel
    #
    cT
    cG
    cbs
    cfv
    #
    wss
    cU
    @22
    wss
    @15
    @10
    wceq
    @1
    @2
    @21
    @3
    cS
    cG
    subgrcl
    3ad2ant1
    @4
    cT
    cS
    @22
    @1
    @2
    @3
    simp2
    #
    @1
    @2
    cS
    @22
    wss
    @3
    @22
    cS
    cG
    @22
    eqid
    #
    subgss
    3ad2ant1
    #
    sstrd
    @4
    cU
    cS
    @22
    @1
    @2
    @3
    simp3
    #
    @25
    sstrd
    vx
    vy
    @22
    @7
    c.po
    cT
    cU
    cG
    cgrp
    @24
    @20
    subglsm.s
    lsmvalx
    syl3anc
    @4
    cH
    cgrp
    wcel
    #
    cT
    cH
    cbs
    cfv
    #
    wss
    cU
    @28
    wss
    @16
    @14
    wceq
    @1
    @2
    @27
    @3
    cS
    cG
    cH
    subglsm.h
    subggrp
    3ad2ant1
    @4
    cT
    cS
    @28
    @23
    @1
    @2
    cS
    @28
    wceq
    @3
    cS
    cG
    cH
    subglsm.h
    subgbas
    3ad2ant1
    #
    sseqtrd
    @4
    cU
    cS
    @28
    @26
    @29
    sseqtrd
    vx
    vy
    @28
    @11
    cA
    cT
    cU
    cH
    cgrp
    @28
    eqid
    @11
    eqid
    subglsm.a
    lsmvalx
    syl3anc
    3eqtr4d
end
