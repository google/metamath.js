include "cvv.mm"
include "wcel.mm"
include "c0.mm"
include "c0g.mm"
include "cfv.mm"
include "wceq.mm"
include "cbs.mm"
include "cplusg.mm"
include "eqid.mm"
include "cword.mm"
include "wrd0.mm"
include "frmdbas.mm"
include "syl5eleqr.mm"
include "cv.mm"
include "wa.mm"
include "co.mm"
include "cconcat.mm"
include "frmdadd.mm"
include "sylan.mm"
include "frmdelbas.mm"
include "adantl.mm"
include "ccatlid.mm"
include "syl.mm"
include "eqtrd.mm"
include "ancoms.mm"
include "ccatrid.mm"
include "ismgmid2.mm"
include "wn.mm"
include "cfrmd.mm"
include "fvprc.mm"
include "syl5eq.mm"
include "fveq2d.mm"
include "0g0.mm"
include "syl6reqr.mm"
include "pm2.61i.mm"

theorem frmd0
  let cI: class I
  let cM: class M
  let cA: class A
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cJ: class J
  let cU: class U
  let cV: class V
  let cW: class W
  assume frmdmnd.m: |- M = ( freeMnd ` I )


  assert |- (/) = ( 0g ` M )

  proof
    cI
    cvv
    wcel
    #
    c0
    cM
    c0g
    cfv
    #
    wceq
    @0
    vx
    cM
    cbs
    cfv
    #
    cM
    cplusg
    cfv
    #
    c0
    cM
    @1
    @2
    eqid
    #
    @1
    eqid
    @3
    eqid
    #
    @0
    c0
    cI
    cword
    #
    @2
    cI
    wrd0
    @2
    cI
    cM
    cvv
    frmdmnd.m
    @4
    frmdbas
    syl5eleqr
    #
    @0
    vx
    cv
    #
    @2
    wcel
    #
    wa
    #
    c0
    @8
    @3
    co
    #
    c0
    @8
    cconcat
    co
    #
    @8
    @0
    c0
    @2
    wcel
    #
    @9
    @11
    @12
    wceq
    @7
    @2
    @3
    cI
    cM
    c0
    @8
    frmdmnd.m
    @4
    @5
    frmdadd
    sylan
    @10
    @8
    @6
    wcel
    #
    @12
    @8
    wceq
    @9
    @14
    @0
    @2
    cI
    cM
    @8
    frmdmnd.m
    @4
    frmdelbas
    adantl
    #
    cI
    @8
    ccatlid
    syl
    eqtrd
    @10
    @8
    c0
    @3
    co
    #
    @8
    c0
    cconcat
    co
    #
    @8
    @0
    @13
    @9
    @16
    @17
    wceq
    #
    @7
    @9
    @13
    @18
    @2
    @3
    cI
    cM
    @8
    c0
    frmdmnd.m
    @4
    @5
    frmdadd
    ancoms
    sylan
    @10
    @14
    @17
    @8
    wceq
    @15
    cI
    @8
    ccatrid
    syl
    eqtrd
    ismgmid2
    @0
    wn
    #
    @1
    c0
    c0g
    cfv
    c0
    @19
    cM
    c0
    c0g
    @19
    cM
    cI
    cfrmd
    cfv
    c0
    frmdmnd.m
    cI
    cfrmd
    fvprc
    syl5eq
    fveq2d
    0g0
    syl6reqr
    pm2.61i
end
