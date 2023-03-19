include "cipf.mm"
include "cfv.mm"
include "co.mm"
include "cmpt.mm"
include "ccn.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "cbs.mm"
include "wceq.mm"
include "wf.mm"
include "wral.mm"
include "ctopon.mm"
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
include "fmpt.mm"
include "sylibr.mm"
include "r19.21bi.mm"
include "ipfval.mm"
include "syl2anc.mm"
include "mpteq2dva.mm"
include "ctx.mm"
include "ipcn.mm"
include "syl.mm"
include "cnmpt12f.mm"
include "eqeltrrd.mm"

theorem cnmpt1ip
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let c.xi: class .,
  let cJ: class J
  let cK: class K
  let cW: class W
  let cX: class X
  let vy: setvar y
  let cY: class Y
  assume cnmpt1ip.j: |- J = ( TopOpen ` W )
  assume cnmpt1ip.c: |- C = ( TopOpen ` CCfld )
  assume cnmpt1ip.h: |- ., = ( .i ` W )
  assume cnmpt1ip.r: |- ( ph -> W e. CPreHil )
  assume cnmpt1ip.k: |- ( ph -> K e. ( TopOn ` X ) )
  assume cnmpt1ip.a: |- ( ph -> ( x e. X |-> A ) e. ( K Cn J ) )
  assume cnmpt1ip.b: |- ( ph -> ( x e. X |-> B ) e. ( K Cn J ) )

  disjoint C x
  disjoint J x
  disjoint K x
  disjoint ph x
  disjoint W x
  disjoint X x
  disjoint x y
  disjoint C y
  disjoint J y
  disjoint ph y
  disjoint W y
  disjoint X y
  disjoint Y x
  disjoint Y y
  assert |- ( ph -> ( x e. X |-> ( A ., B ) ) e. ( K Cn C ) )

  proof
    wph
    vx
    cX
    cA
    cB
    cW
    cipf
    cfv
    #
    co
    #
    cmpt
    vx
    cX
    cA
    cB
    c.xi
    co
    #
    cmpt
    cK
    cC
    ccn
    co
    wph
    vx
    cX
    @1
    @2
    wph
    vx
    cv
    cX
    wcel
    wa
    cA
    cW
    cbs
    cfv
    #
    wcel
    #
    cB
    @3
    wcel
    #
    @1
    @2
    wceq
    wph
    @4
    vx
    cX
    wph
    cX
    @3
    vx
    cX
    cA
    cmpt
    #
    wf
    #
    @4
    vx
    cX
    wral
    wph
    cK
    cX
    ctopon
    cfv
    wcel
    #
    cJ
    @3
    ctopon
    cfv
    wcel
    #
    @6
    cK
    cJ
    ccn
    co
    #
    wcel
    @7
    cnmpt1ip.k
    wph
    cW
    ctps
    wcel
    #
    @9
    wph
    cW
    ccph
    wcel
    #
    cW
    cngp
    wcel
    @11
    cnmpt1ip.r
    cW
    cphngp
    cW
    ngptps
    3syl
    @3
    cJ
    cW
    @3
    eqid
    #
    cnmpt1ip.j
    istps
    sylib
    #
    cnmpt1ip.a
    @6
    cK
    cJ
    cX
    @3
    cnf2
    syl3anc
    vx
    cX
    @3
    cA
    @6
    @6
    eqid
    fmpt
    sylibr
    r19.21bi
    wph
    @5
    vx
    cX
    wph
    cX
    @3
    vx
    cX
    cB
    cmpt
    #
    wf
    #
    @5
    vx
    cX
    wral
    wph
    @8
    @9
    @15
    @10
    wcel
    @16
    cnmpt1ip.k
    @14
    cnmpt1ip.b
    @15
    cK
    cJ
    cX
    @3
    cnf2
    syl3anc
    vx
    cX
    @3
    cB
    @15
    @15
    eqid
    fmpt
    sylibr
    r19.21bi
    @0
    c.xi
    @3
    cW
    cA
    cB
    @13
    cnmpt1ip.h
    @0
    eqid
    #
    ipfval
    syl2anc
    mpteq2dva
    wph
    vx
    cA
    cB
    @0
    cK
    cJ
    cJ
    cC
    cX
    cnmpt1ip.k
    cnmpt1ip.a
    cnmpt1ip.b
    wph
    @12
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
    @17
    cnmpt1ip.j
    cnmpt1ip.c
    ipcn
    syl
    cnmpt12f
    eqeltrrd
end
