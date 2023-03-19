include "clmod.mm"
include "wcel.mm"
include "cbs.mm"
include "cfv.mm"
include "c0g.mm"
include "csn.mm"
include "cdif.mm"
include "cv.mm"
include "clspn.mm"
include "cmpt.mm"
include "crn.mm"
include "eqid.mm"
include "lsatset.mm"
include "wf.mm"
include "wss.mm"
include "eldifi.mm"
include "lspsncl.mm"
include "sylan2.mm"
include "fmptd.mm"
include "frn.mm"
include "syl.mm"
include "eqsstrd.mm"

theorem lsatlss
  let cA: class A
  let cS: class S
  let cW: class W
  let vv: setvar v
  assume lsatlss.s: |- S = ( LSubSp ` W )
  assume lsatlss.a: |- A = ( LSAtoms ` W )


  assert |- ( W e. LMod -> A C_ S )

  proof
    cW
    clmod
    wcel
    #
    cA
    vv
    cW
    cbs
    cfv
    #
    cW
    c0g
    cfv
    #
    csn
    #
    cdif
    #
    vv
    cv
    #
    csn
    cW
    clspn
    cfv
    #
    cfv
    #
    cmpt
    #
    crn
    #
    cS
    vv
    cA
    @6
    @1
    cW
    clmod
    @2
    @1
    eqid
    #
    @6
    eqid
    #
    @2
    eqid
    lsatlss.a
    lsatset
    @0
    @4
    cS
    @8
    wf
    @9
    cS
    wss
    @0
    vv
    @4
    @7
    cS
    @8
    @5
    @4
    wcel
    @0
    @5
    @1
    wcel
    @7
    cS
    wcel
    @5
    @1
    @3
    eldifi
    cS
    @6
    @1
    cW
    @5
    @10
    lsatlss.s
    @11
    lspsncl
    sylan2
    @8
    eqid
    fmptd
    @4
    cS
    @8
    frn
    syl
    eqsstrd
end
