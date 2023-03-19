include "cfv.mm"
include "co.mm"
include "csg.mm"
include "fveq2i.mm"
include "fveq1i.mm"
include "wcel.mm"
include "wceq.mm"
include "evl1vard.mm"
include "evl1scad.mm"
include "eqid.mm"
include "evl1subd.mm"
include "simprd.mm"
include "syl5eq.mm"

theorem lineval
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cP: class P
  let cR: class R
  let cG: class G
  let cK: class K
  let c.mi: class .-
  let cO: class O
  let cV: class V
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
  assume lineval.o: |- O = ( eval1 ` R )
  assume lineval.r: |- ( ph -> R e. CRing )
  assume lineval.v: |- ( ph -> V e. K )


  assert |- ( ph -> ( ( O ` G ) ` V ) = ( V ( -g ` R ) C ) )

  proof
    wph
    cV
    cG
    cO
    cfv
    #
    cfv
    cV
    cX
    cC
    cA
    cfv
    #
    c.mi
    co
    #
    cO
    cfv
    #
    cfv
    #
    cV
    cC
    cR
    csg
    cfv
    #
    co
    #
    cV
    @0
    @3
    cG
    @2
    cO
    linply1.g
    fveq2i
    fveq1i
    wph
    @2
    cB
    wcel
    @4
    @6
    wceq
    wph
    cK
    @5
    cP
    cR
    cB
    cX
    c.mi
    @1
    cO
    cV
    cC
    cV
    lineval.o
    linply1.p
    linply1.k
    linply1.b
    lineval.r
    lineval.v
    wph
    cK
    cP
    cR
    cB
    cO
    cX
    cV
    lineval.o
    linply1.x
    linply1.k
    linply1.p
    linply1.b
    lineval.r
    lineval.v
    evl1vard
    wph
    cA
    cK
    cP
    cR
    cB
    cO
    cC
    cV
    lineval.o
    linply1.p
    linply1.k
    linply1.a
    linply1.b
    lineval.r
    linply1.c
    lineval.v
    evl1scad
    linply1.m
    @5
    eqid
    evl1subd
    simprd
    syl5eq
end
