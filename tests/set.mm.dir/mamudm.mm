include "wcel.mm"
include "cfn.mm"
include "w3a.mm"
include "wa.mm"
include "cdm.mm"
include "cbs.mm"
include "cfv.mm"
include "cxp.mm"
include "cmap.mm"
include "co.mm"
include "cv.mm"
include "cmulr.mm"
include "cmpt.mm"
include "cgsu.mm"
include "cmpt2.mm"
include "eqid.mm"
include "simpl.mm"
include "simpr1.mm"
include "simpr2.mm"
include "simpr3.mm"
include "mamufval.mm"
include "dmeqd.mm"
include "cvv.mm"
include "wral.mm"
include "wceq.mm"
include "mpt2exga.mm"
include "3adant2.mm"
include "adantl.mm"
include "a1d.mm"
include "ralrimivv.mm"
include "dmmpt2ga.mm"
include "syl.mm"
include "xpfi.mm"
include "3adant3.mm"
include "frlmfibas.mm"
include "sylan2.mm"
include "syl6eqr.mm"
include "3adant1.mm"
include "xpeq12d.mm"
include "3eqtrd.mm"

theorem mamudm
  let cB: class B
  let cC: class C
  let cP: class P
  let cR: class R
  let c.xp: class .X.
  let cE: class E
  let cF: class F
  let cM: class M
  let cN: class N
  let cV: class V
  let vi: setvar i
  let vj: setvar j
  let vk: setvar k
  let vx: setvar x
  let vy: setvar y
  assume mamudm.e: |- E = ( R freeLMod ( M X. N ) )
  assume mamudm.b: |- B = ( Base ` E )
  assume mamudm.f: |- F = ( R freeLMod ( N X. P ) )
  assume mamudm.c: |- C = ( Base ` F )
  assume mamudm.m: |- .X. = ( R maMul <. M , N , P >. )


  assert |- ( ( R e. V /\ ( M e. Fin /\ N e. Fin /\ P e. Fin ) ) -> dom .X. = ( B X. C ) )

  proof
    cR
    cV
    wcel
    #
    cM
    cfn
    wcel
    #
    cN
    cfn
    wcel
    #
    cP
    cfn
    wcel
    #
    w3a
    #
    wa
    #
    c.xp
    cdm
    vx
    vy
    cR
    cbs
    cfv
    #
    cM
    cN
    cxp
    #
    cmap
    co
    #
    @6
    cN
    cP
    cxp
    #
    cmap
    co
    #
    vi
    vk
    cM
    cP
    cR
    vj
    cN
    vi
    cv
    vj
    cv
    #
    vx
    cv
    #
    co
    @11
    vk
    cv
    vy
    cv
    #
    co
    cR
    cmulr
    cfv
    #
    co
    cmpt
    cgsu
    co
    #
    cmpt2
    #
    cmpt2
    #
    cdm
    #
    @8
    @10
    cxp
    #
    cB
    cC
    cxp
    @5
    c.xp
    @17
    @5
    vx
    vy
    @6
    cP
    cR
    @14
    vi
    vj
    vk
    c.xp
    cM
    cN
    cV
    mamudm.m
    @6
    eqid
    #
    @14
    eqid
    @0
    @4
    simpl
    @0
    @1
    @2
    @3
    simpr1
    @0
    @1
    @2
    @3
    simpr2
    @0
    @1
    @2
    @3
    simpr3
    mamufval
    dmeqd
    @5
    @16
    cvv
    wcel
    #
    vy
    @10
    wral
    vx
    @8
    wral
    @18
    @19
    wceq
    @5
    @21
    vx
    vy
    @8
    @10
    @5
    @21
    @12
    @8
    wcel
    @13
    @10
    wcel
    wa
    @4
    @21
    @0
    @1
    @3
    @21
    @2
    vi
    vk
    cM
    cP
    @15
    cfn
    cfn
    mpt2exga
    3adant2
    adantl
    a1d
    ralrimivv
    vx
    vy
    @8
    @10
    @16
    @17
    cvv
    @17
    eqid
    dmmpt2ga
    syl
    @5
    @8
    cB
    @10
    cC
    @5
    @8
    cE
    cbs
    cfv
    #
    cB
    @4
    @0
    @7
    cfn
    wcel
    #
    @8
    @22
    wceq
    @1
    @2
    @23
    @3
    cM
    cN
    xpfi
    3adant3
    cR
    cE
    @7
    @6
    cV
    mamudm.e
    @20
    frlmfibas
    sylan2
    mamudm.b
    syl6eqr
    @5
    @10
    cF
    cbs
    cfv
    #
    cC
    @4
    @0
    @9
    cfn
    wcel
    #
    @10
    @24
    wceq
    @2
    @3
    @25
    @1
    cN
    cP
    xpfi
    3adant1
    cR
    cF
    @9
    @6
    cV
    mamudm.f
    @20
    frlmfibas
    sylan2
    mamudm.c
    syl6eqr
    xpeq12d
    3eqtrd
end
