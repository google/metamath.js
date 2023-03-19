include "cgrp.mm"
include "wcel.mm"
include "cfn.mm"
include "cprime.mm"
include "w3a.mm"
include "c0g.mm"
include "cfv.mm"
include "csn.mm"
include "cv.mm"
include "wss.mm"
include "cslw.mm"
include "co.mm"
include "wrex.mm"
include "c0.mm"
include "wne.mm"
include "csubg.mm"
include "cress.mm"
include "cpgp.mm"
include "wbr.mm"
include "eqid.mm"
include "0subg.mm"
include "3ad2ant1.mm"
include "simp2.mm"
include "pgp0.mm"
include "3adant2.mm"
include "wa.mm"
include "crab.mm"
include "chash.mm"
include "cmpt.mm"
include "pgpssslw.mm"
include "syl3anc.mm"
include "rexn0.mm"
include "syl.mm"

theorem slwn0
  let cP: class P
  let cG: class G
  let cX: class X
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume slwn0.1: |- X = ( Base ` G )


  assert |- ( ( G e. Grp /\ X e. Fin /\ P e. Prime ) -> ( P pSyl G ) =/= (/) )

  proof
    cG
    cgrp
    wcel
    #
    cX
    cfn
    wcel
    #
    cP
    cprime
    wcel
    #
    w3a
    #
    cG
    c0g
    cfv
    #
    csn
    #
    vz
    cv
    wss
    #
    vz
    cP
    cG
    cslw
    co
    #
    wrex
    #
    @7
    c0
    wne
    @3
    @5
    cG
    csubg
    cfv
    #
    wcel
    #
    @1
    cP
    cG
    @5
    cress
    co
    #
    cpgp
    wbr
    #
    @8
    @0
    @1
    @10
    @2
    cG
    @4
    @4
    eqid
    #
    0subg
    3ad2ant1
    @0
    @1
    @2
    simp2
    @0
    @2
    @12
    @1
    cP
    cG
    @4
    @13
    pgp0
    3adant2
    vx
    vy
    cP
    @11
    vz
    vx
    cP
    cG
    vy
    cv
    #
    cress
    co
    cpgp
    wbr
    @5
    @14
    wss
    wa
    vy
    @9
    crab
    vx
    cv
    chash
    cfv
    cmpt
    #
    cG
    @5
    cX
    slwn0.1
    @11
    eqid
    @15
    eqid
    pgpssslw
    syl3anc
    @6
    vz
    @7
    rexn0
    syl
end
