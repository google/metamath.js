include "cgrp.mm"
include "wcel.mm"
include "c1o.mm"
include "cen.mm"
include "wbr.mm"
include "wa.mm"
include "cmg.mm"
include "cfv.mm"
include "c0g.mm"
include "eqid.mm"
include "simpl.mm"
include "grpidcl.mm"
include "adantr.mm"
include "cv.mm"
include "cc0.mm"
include "cz.mm"
include "co.mm"
include "wceq.mm"
include "wrex.mm"
include "0z.mm"
include "csn.mm"
include "en1eqsn.mm"
include "sylan.mm"
include "eleq2d.mm"
include "biimpa.mm"
include "velsn.mm"
include "sylib.mm"
include "mulg0.mm"
include "syl.mm"
include "eqtr4d.mm"
include "oveq1.mm"
include "eqeq2d.mm"
include "rspcev.mm"
include "sylancr.mm"
include "iscygd.mm"

theorem 0cyg
  let cB: class B
  let cG: class G
  let vm: setvar m
  let vn: setvar n
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cC: class C
  let cF: class F
  let va: setvar a
  let vb: setvar b
  let cE: class E
  let cH: class H
  assume cygctb.1: |- B = ( Base ` G )


  assert |- ( ( G e. Grp /\ B ~~ 1o ) -> G e. CycGrp )

  proof
    cG
    cgrp
    wcel
    #
    cB
    c1o
    cen
    wbr
    #
    wa
    #
    vx
    cB
    cG
    cmg
    cfv
    #
    vn
    cG
    cG
    c0g
    cfv
    #
    cygctb.1
    @3
    eqid
    #
    @0
    @1
    simpl
    @0
    @4
    cB
    wcel
    #
    @1
    cB
    cG
    @4
    cygctb.1
    @4
    eqid
    #
    grpidcl
    #
    adantr
    #
    @2
    vx
    cv
    #
    cB
    wcel
    #
    wa
    #
    cc0
    cz
    wcel
    @10
    cc0
    @4
    @3
    co
    #
    wceq
    #
    @10
    vn
    cv
    #
    @4
    @3
    co
    #
    wceq
    #
    vn
    cz
    wrex
    0z
    @12
    @10
    @4
    @13
    @12
    @10
    @4
    csn
    #
    wcel
    #
    @10
    @4
    wceq
    @2
    @11
    @19
    @2
    cB
    @18
    @10
    @0
    @6
    @1
    cB
    @18
    wceq
    @8
    @4
    cB
    en1eqsn
    sylan
    eleq2d
    biimpa
    vx
    @4
    velsn
    sylib
    @2
    @13
    @4
    wceq
    #
    @11
    @2
    @6
    @20
    @9
    cB
    @3
    cG
    @4
    @4
    cygctb.1
    @7
    @5
    mulg0
    syl
    adantr
    eqtr4d
    @17
    @14
    vn
    cc0
    cz
    @15
    cc0
    wceq
    @16
    @13
    @10
    @15
    cc0
    @4
    @3
    oveq1
    eqeq2d
    rspcev
    sylancr
    iscygd
end
