include "cabl.mm"
include "wcel.mm"
include "csubg.mm"
include "cfv.mm"
include "wa.mm"
include "cplusg.mm"
include "cbs.mm"
include "wceq.mm"
include "subgbas.mm"
include "adantl.mm"
include "eqid.mm"
include "ressplusg.mm"
include "cgrp.mm"
include "subggrp.mm"
include "cv.mm"
include "w3a.mm"
include "co.mm"
include "simp1l.mm"
include "wss.mm"
include "simp1r.mm"
include "subgss.mm"
include "syl.mm"
include "simp2.mm"
include "sseldd.mm"
include "simp3.mm"
include "ablcom.mm"
include "syl3anc.mm"
include "isabld.mm"

theorem subgabl
  let cS: class S
  let cG: class G
  let cH: class H
  let vx: setvar x
  let vy: setvar y
  assume subgabl.h: |- H = ( G |`s S )


  assert |- ( ( G e. Abel /\ S e. ( SubGrp ` G ) ) -> H e. Abel )

  proof
    cG
    cabl
    wcel
    #
    cS
    cG
    csubg
    cfv
    #
    wcel
    #
    wa
    #
    vx
    vy
    cS
    cG
    cplusg
    cfv
    #
    cH
    @2
    cS
    cH
    cbs
    cfv
    wceq
    @0
    cS
    cG
    cH
    subgabl.h
    subgbas
    adantl
    @2
    @4
    cH
    cplusg
    cfv
    wceq
    @0
    cS
    @4
    cG
    cH
    @1
    subgabl.h
    @4
    eqid
    #
    ressplusg
    adantl
    @2
    cH
    cgrp
    wcel
    @0
    cS
    cG
    cH
    subgabl.h
    subggrp
    adantl
    @3
    vx
    cv
    #
    cS
    wcel
    #
    vy
    cv
    #
    cS
    wcel
    #
    w3a
    #
    @0
    @6
    cG
    cbs
    cfv
    #
    wcel
    @8
    @11
    wcel
    @6
    @8
    @4
    co
    @8
    @6
    @4
    co
    wceq
    @0
    @2
    @7
    @9
    simp1l
    @10
    cS
    @11
    @6
    @10
    @2
    cS
    @11
    wss
    @0
    @2
    @7
    @9
    simp1r
    @11
    cS
    cG
    @11
    eqid
    #
    subgss
    syl
    #
    @3
    @7
    @9
    simp2
    sseldd
    @10
    cS
    @11
    @8
    @13
    @3
    @7
    @9
    simp3
    sseldd
    @11
    @4
    cG
    @6
    @8
    @12
    @5
    ablcom
    syl3anc
    isabld
end
