include "cfv.mm"
include "co.mm"
include "cgrp.mm"
include "wcel.mm"
include "crg.mm"
include "ply1ring.mm"
include "ringgrp.mm"
include "3syl.mm"
include "vr1cl.mm"
include "syl.mm"
include "wf.mm"
include "ply1sclf.mm"
include "ffvelrnd.mm"
include "grpsubcl.mm"
include "syl3anc.mm"
include "syl5eqel.mm"

theorem linply1
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cP: class P
  let cR: class R
  let cG: class G
  let cK: class K
  let c.mi: class .-
  let cX: class X
  let vk: setvar k
  let vx: setvar x
  assume linply1.p: |- P = ( Poly1 ` R )
  assume linply1.b: |- B = ( Base ` P )
  assume linply1.k: |- K = ( Base ` R )
  assume linply1.x: |- X = ( var1 ` R )
  assume linply1.m: |- .- = ( -g ` P )
  assume linply1.a: |- A = ( algSc ` P )
  assume linply1.g: |- G = ( X .- ( A ` C ) )
  assume linply1.c: |- ( ph -> C e. K )
  assume linply1.r: |- ( ph -> R e. Ring )


  assert |- ( ph -> G e. B )

  proof
    wph
    cG
    cX
    cC
    cA
    cfv
    #
    c.mi
    co
    #
    cB
    linply1.g
    wph
    cP
    cgrp
    wcel
    #
    cX
    cB
    wcel
    #
    @0
    cB
    wcel
    @1
    cB
    wcel
    wph
    cR
    crg
    wcel
    #
    cP
    crg
    wcel
    @2
    linply1.r
    cP
    cR
    linply1.p
    ply1ring
    cP
    ringgrp
    3syl
    wph
    @4
    @3
    linply1.r
    cB
    cP
    cR
    cX
    linply1.x
    linply1.p
    linply1.b
    vr1cl
    syl
    wph
    cK
    cB
    cC
    cA
    wph
    @4
    cK
    cB
    cA
    wf
    linply1.r
    cA
    cB
    cP
    cR
    cK
    linply1.p
    linply1.a
    linply1.k
    linply1.b
    ply1sclf
    syl
    linply1.c
    ffvelrnd
    cB
    cP
    c.mi
    cX
    @0
    linply1.b
    linply1.m
    grpsubcl
    syl3anc
    syl5eqel
end
