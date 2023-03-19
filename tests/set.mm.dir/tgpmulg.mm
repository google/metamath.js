include "ctgp.mm"
include "wcel.mm"
include "cz.mm"
include "wa.mm"
include "cn0.mm"
include "cv.mm"
include "co.mm"
include "cmpt.mm"
include "ccn.mm"
include "cr.mm"
include "cneg.mm"
include "cn.mm"
include "ctmd.mm"
include "tgptmd.mm"
include "tmdmulg.mm"
include "sylan.mm"
include "adantlr.mm"
include "cminusg.mm"
include "cfv.mm"
include "simpllr.mm"
include "zcnd.mm"
include "negnegd.mm"
include "oveq1d.mm"
include "wceq.mm"
include "eqid.mm"
include "mulgnegnn.mm"
include "adantll.mm"
include "eqtr3d.mm"
include "mpteq2dva.mm"
include "ctopon.mm"
include "tgptopon.mm"
include "ad2antrr.mm"
include "adantr.mm"
include "nnnn0.mm"
include "syl2an.mm"
include "tgpinv.mm"
include "cnmpt11f.mm"
include "eqeltrd.mm"
include "adantrl.mm"
include "wo.mm"
include "simpr.mm"
include "elznn0nn.mm"
include "sylib.mm"
include "mpjaodan.mm"

theorem tgpmulg
  let vx: setvar x
  let cB: class B
  let c.x: class .x.
  let cG: class G
  let cJ: class J
  let cN: class N
  let vk: setvar k
  let vn: setvar n
  let vy: setvar y
  assume tgpmulg.j: |- J = ( TopOpen ` G )
  assume tgpmulg.t: |- .x. = ( .g ` G )
  assume tgpmulg.b: |- B = ( Base ` G )

  disjoint B x
  disjoint G x
  disjoint J x
  disjoint .x. x
  disjoint N x
  disjoint k n
  disjoint k x
  disjoint k y
  disjoint B k
  disjoint n x
  disjoint n y
  disjoint B n
  disjoint x y
  disjoint B y
  disjoint G k
  disjoint G n
  disjoint G y
  disjoint J k
  disjoint J n
  disjoint J y
  disjoint .x. k
  disjoint .x. n
  disjoint .x. y
  disjoint N n
  assert |- ( ( G e. TopGrp /\ N e. ZZ ) -> ( x e. B |-> ( N .x. x ) ) e. ( J Cn J ) )

  proof
    cG
    ctgp
    wcel
    #
    cN
    cz
    wcel
    #
    wa
    #
    cN
    cn0
    wcel
    #
    vx
    cB
    cN
    vx
    cv
    #
    c.x
    co
    #
    cmpt
    #
    cJ
    cJ
    ccn
    co
    #
    wcel
    #
    cN
    cr
    wcel
    #
    cN
    cneg
    #
    cn
    wcel
    #
    wa
    #
    @0
    @3
    @8
    @1
    @0
    cG
    ctmd
    wcel
    #
    @3
    @8
    cG
    tgptmd
    #
    vx
    cB
    c.x
    cG
    cJ
    cN
    tgpmulg.j
    tgpmulg.t
    tgpmulg.b
    tmdmulg
    sylan
    adantlr
    @2
    @11
    @8
    @9
    @2
    @11
    wa
    #
    @6
    vx
    cB
    @10
    @4
    c.x
    co
    #
    cG
    cminusg
    cfv
    #
    cfv
    #
    cmpt
    @7
    @15
    vx
    cB
    @5
    @18
    @15
    @4
    cB
    wcel
    #
    wa
    #
    @10
    cneg
    #
    @4
    c.x
    co
    #
    @5
    @18
    @20
    @21
    cN
    @4
    c.x
    @20
    cN
    @20
    cN
    @0
    @1
    @11
    @19
    simpllr
    zcnd
    negnegd
    oveq1d
    @11
    @19
    @22
    @18
    wceq
    @2
    cB
    c.x
    cG
    @17
    @10
    @4
    tgpmulg.b
    tgpmulg.t
    @17
    eqid
    #
    mulgnegnn
    adantll
    eqtr3d
    mpteq2dva
    @15
    vx
    @16
    @17
    cJ
    cJ
    cJ
    cB
    @0
    cJ
    cB
    ctopon
    cfv
    wcel
    @1
    @11
    cG
    cJ
    cB
    tgpmulg.j
    tgpmulg.b
    tgptopon
    ad2antrr
    @2
    @13
    @10
    cn0
    wcel
    vx
    cB
    @16
    cmpt
    @7
    wcel
    @11
    @0
    @13
    @1
    @14
    adantr
    @10
    nnnn0
    vx
    cB
    c.x
    cG
    cJ
    @10
    tgpmulg.j
    tgpmulg.t
    tgpmulg.b
    tmdmulg
    syl2an
    @0
    @17
    @7
    wcel
    @1
    @11
    cG
    @17
    cJ
    tgpmulg.j
    @23
    tgpinv
    ad2antrr
    cnmpt11f
    eqeltrd
    adantrl
    @2
    @1
    @3
    @12
    wo
    @0
    @1
    simpr
    cN
    elznn0nn
    sylib
    mpjaodan
end
