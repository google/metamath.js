include "wcel.mm"
include "c0.mm"
include "wne.mm"
include "wa.mm"
include "cfn.mm"
include "w3a.mm"
include "co.mm"
include "wceq.mm"
include "wi.mm"
include "2a1.mm"
include "wn.mm"
include "cdm.mm"
include "cxp.mm"
include "mamudm.mm"
include "adantlr.mm"
include "3adant1.mm"
include "adantl.mm"
include "simpl.mm"
include "intnand.mm"
include "ndmovg.mm"
include "syl2anc.mm"
include "eqeq1.mm"
include "xpfi.mm"
include "3adant2.mm"
include "xpnz.mm"
include "biimpi.mm"
include "cbs.mm"
include "cfv.mm"
include "eqid.mm"
include "elfrlmbasn0.mm"
include "syl2an.mm"
include "ex.mm"
include "com13.mm"
include "com12.mm"
include "3imp.mm"
include "eqneqall.mm"
include "syl5com.mm"
include "eqcoms.mm"
include "syl6bi.mm"
include "com23.mm"
include "mpcom.mm"
include "pm2.61i.mm"

theorem mamufacex
  let cB: class B
  let cC: class C
  let cD: class D
  let cP: class P
  let cR: class R
  let c.xp: class .X.
  let cE: class E
  let cF: class F
  let cG: class G
  let cM: class M
  let cN: class N
  let cV: class V
  let cX: class X
  let cY: class Y
  let cZ: class Z
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
  assume mamufacex.g: |- G = ( R freeLMod ( M X. P ) )
  assume mamufacex.d: |- D = ( Base ` G )


  assert |- ( ( ( M =/= (/) /\ P =/= (/) ) /\ ( R e. V /\ Y e. D ) /\ ( M e. Fin /\ N e. Fin /\ P e. Fin ) ) -> ( ( X .X. Z ) = Y -> Z e. C ) )

  proof
    cZ
    cC
    wcel
    #
    cM
    c0
    wne
    cP
    c0
    wne
    wa
    #
    cR
    cV
    wcel
    #
    cY
    cD
    wcel
    #
    wa
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
    w3a
    #
    cX
    cZ
    c.xp
    co
    #
    cY
    wceq
    #
    @0
    wi
    #
    wi
    @0
    @9
    @11
    2a1
    @0
    wn
    #
    @9
    @12
    @10
    c0
    wceq
    #
    @13
    @9
    wa
    #
    @12
    @15
    c.xp
    cdm
    cB
    cC
    cxp
    wceq
    #
    cX
    cB
    wcel
    #
    @0
    wa
    wn
    @14
    @9
    @16
    @13
    @4
    @8
    @16
    @1
    @2
    @8
    @16
    @3
    cB
    cC
    cP
    cR
    c.xp
    cE
    cF
    cM
    cN
    cV
    mamudm.e
    mamudm.b
    mamudm.f
    mamudm.c
    mamudm.m
    mamudm
    adantlr
    3adant1
    adantl
    @15
    @0
    @17
    @13
    @9
    simpl
    intnand
    cX
    cZ
    cB
    cC
    c.xp
    ndmovg
    syl2anc
    @14
    @11
    @15
    @0
    @14
    @11
    c0
    cY
    wceq
    @15
    @0
    wi
    #
    @10
    c0
    cY
    eqeq1
    @18
    cY
    c0
    @15
    cY
    c0
    wceq
    #
    @0
    @9
    @19
    @0
    wi
    @13
    @9
    cY
    c0
    wne
    #
    @19
    @0
    @1
    @4
    @8
    @20
    @4
    @1
    @8
    @20
    wi
    #
    @3
    @1
    @21
    wi
    @2
    @8
    @1
    @3
    @20
    @8
    @1
    @3
    @20
    wi
    #
    @8
    cM
    cP
    cxp
    #
    cfn
    wcel
    #
    @23
    c0
    wne
    #
    @22
    @1
    @5
    @7
    @24
    @6
    cM
    cP
    xpfi
    3adant2
    @1
    @25
    cM
    cP
    xpnz
    biimpi
    cD
    cR
    cG
    @23
    cR
    cbs
    cfv
    #
    cfn
    cY
    mamufacex.g
    @26
    eqid
    mamufacex.d
    elfrlmbasn0
    syl2an
    ex
    com13
    adantl
    com12
    3imp
    @0
    cY
    c0
    eqneqall
    syl5com
    adantl
    com12
    eqcoms
    syl6bi
    com23
    mpcom
    ex
    pm2.61i
end
