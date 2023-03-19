include "cipf.mm"
include "cfv.mm"
include "co.mm"
include "cmpt2.mm"
include "ctx.mm"
include "ccn.mm"
include "cv.mm"
include "wcel.mm"
include "wceq.mm"
include "wa.mm"
include "cbs.mm"
include "wral.mm"
include "cxp.mm"
include "wf.mm"
include "ctopon.mm"
include "txtopon.mm"
include "syl2anc.mm"
include "ctps.mm"
include "ccph.mm"
include "cngp.mm"
include "cphngp.mm"
include "ngptps.mm"
include "3syl.mm"
include "eqid.mm"
include "istps.mm"
include "sylib.mm"
include "cnf2.mm"
include "syl3anc.mm"
include "fmpt2.mm"
include "sylibr.mm"
include "r19.21bi.mm"
include "ipfval.mm"
include "3impa.mm"
include "mpt2eq3dva.mm"
include "ipcn.mm"
include "syl.mm"
include "cnmpt22f.mm"
include "eqeltrrd.mm"

theorem cnmpt2ip
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let c.xi: class .,
  let cJ: class J
  let cK: class K
  let cL: class L
  let cW: class W
  let cX: class X
  let cY: class Y
  assume cnmpt1ip.j: |- J = ( TopOpen ` W )
  assume cnmpt1ip.c: |- C = ( TopOpen ` CCfld )
  assume cnmpt1ip.h: |- ., = ( .i ` W )
  assume cnmpt1ip.r: |- ( ph -> W e. CPreHil )
  assume cnmpt1ip.k: |- ( ph -> K e. ( TopOn ` X ) )
  assume cnmpt2ip.l: |- ( ph -> L e. ( TopOn ` Y ) )
  assume cnmpt2ip.a: |- ( ph -> ( x e. X , y e. Y |-> A ) e. ( ( K tX L ) Cn J ) )
  assume cnmpt2ip.b: |- ( ph -> ( x e. X , y e. Y |-> B ) e. ( ( K tX L ) Cn J ) )

  disjoint x y
  disjoint C x
  disjoint C y
  disjoint J x
  disjoint J y
  disjoint K x
  disjoint ph x
  disjoint ph y
  disjoint W x
  disjoint W y
  disjoint X x
  disjoint X y
  disjoint Y x
  disjoint Y y
  assert |- ( ph -> ( x e. X , y e. Y |-> ( A ., B ) ) e. ( ( K tX L ) Cn C ) )

  proof
    wph
    vx
    vy
    cX
    cY
    cA
    cB
    cW
    cipf
    cfv
    #
    co
    #
    cmpt2
    vx
    vy
    cX
    cY
    cA
    cB
    c.xi
    co
    #
    cmpt2
    cK
    cL
    ctx
    co
    #
    cC
    ccn
    co
    wph
    vx
    vy
    cX
    cY
    @1
    @2
    wph
    vx
    cv
    cX
    wcel
    #
    vy
    cv
    cY
    wcel
    #
    @1
    @2
    wceq
    #
    wph
    @4
    wa
    #
    @5
    wa
    cA
    cW
    cbs
    cfv
    #
    wcel
    #
    cB
    @8
    wcel
    #
    @6
    @7
    @9
    vy
    cY
    wph
    @9
    vy
    cY
    wral
    #
    vx
    cX
    wph
    cX
    cY
    cxp
    #
    @8
    vx
    vy
    cX
    cY
    cA
    cmpt2
    #
    wf
    #
    @11
    vx
    cX
    wral
    wph
    @3
    @12
    ctopon
    cfv
    wcel
    #
    cJ
    @8
    ctopon
    cfv
    wcel
    #
    @13
    @3
    cJ
    ccn
    co
    #
    wcel
    @14
    wph
    cK
    cX
    ctopon
    cfv
    wcel
    cL
    cY
    ctopon
    cfv
    wcel
    @15
    cnmpt1ip.k
    cnmpt2ip.l
    cK
    cL
    cX
    cY
    txtopon
    syl2anc
    #
    wph
    cW
    ctps
    wcel
    #
    @16
    wph
    cW
    ccph
    wcel
    #
    cW
    cngp
    wcel
    @19
    cnmpt1ip.r
    cW
    cphngp
    cW
    ngptps
    3syl
    @8
    cJ
    cW
    @8
    eqid
    #
    cnmpt1ip.j
    istps
    sylib
    #
    cnmpt2ip.a
    @13
    @3
    cJ
    @12
    @8
    cnf2
    syl3anc
    vx
    vy
    cX
    cY
    cA
    @8
    @13
    @13
    eqid
    fmpt2
    sylibr
    r19.21bi
    r19.21bi
    @7
    @10
    vy
    cY
    wph
    @10
    vy
    cY
    wral
    #
    vx
    cX
    wph
    @12
    @8
    vx
    vy
    cX
    cY
    cB
    cmpt2
    #
    wf
    #
    @23
    vx
    cX
    wral
    wph
    @15
    @16
    @24
    @17
    wcel
    @25
    @18
    @22
    cnmpt2ip.b
    @24
    @3
    cJ
    @12
    @8
    cnf2
    syl3anc
    vx
    vy
    cX
    cY
    cB
    @8
    @24
    @24
    eqid
    fmpt2
    sylibr
    r19.21bi
    r19.21bi
    @0
    c.xi
    @8
    cW
    cA
    cB
    @21
    cnmpt1ip.h
    @0
    eqid
    #
    ipfval
    syl2anc
    3impa
    mpt2eq3dva
    wph
    vx
    vy
    cA
    cB
    @0
    cK
    cL
    cJ
    cJ
    cC
    cX
    cY
    cnmpt1ip.k
    cnmpt2ip.l
    cnmpt2ip.a
    cnmpt2ip.b
    wph
    @20
    @0
    cJ
    cJ
    ctx
    co
    cC
    ccn
    co
    wcel
    cnmpt1ip.r
    @0
    cJ
    cC
    cW
    @26
    cnmpt1ip.j
    cnmpt1ip.c
    ipcn
    syl
    cnmpt22f
    eqeltrrd
end
