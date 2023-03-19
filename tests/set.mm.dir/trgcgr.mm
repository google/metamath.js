include "cs3.mm"
include "wbr.mm"
include "co.mm"
include "wceq.mm"
include "trgcgrg.mm"
include "mpbir3and.mm"

theorem trgcgr
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cP: class P
  let c.sm: class .~
  let cE: class E
  let cF: class F
  let cG: class G
  let c.mi: class .-
  let vi: setvar i
  let vj: setvar j
  assume trgcgrg.p: |- P = ( Base ` G )
  assume trgcgrg.m: |- .- = ( dist ` G )
  assume trgcgrg.r: |- .~ = ( cgrG ` G )
  assume trgcgrg.g: |- ( ph -> G e. TarskiG )
  assume trgcgrg.a: |- ( ph -> A e. P )
  assume trgcgrg.b: |- ( ph -> B e. P )
  assume trgcgrg.c: |- ( ph -> C e. P )
  assume trgcgrg.d: |- ( ph -> D e. P )
  assume trgcgrg.e: |- ( ph -> E e. P )
  assume trgcgrg.f: |- ( ph -> F e. P )
  assume trgcgr.1: |- ( ph -> ( A .- B ) = ( D .- E ) )
  assume trgcgr.2: |- ( ph -> ( B .- C ) = ( E .- F ) )
  assume trgcgr.3: |- ( ph -> ( C .- A ) = ( F .- D ) )


  assert |- ( ph -> <" A B C "> .~ <" D E F "> )

  proof
    wph
    cA
    cB
    cC
    cs3
    cD
    cE
    cF
    cs3
    c.sm
    wbr
    cA
    cB
    c.mi
    co
    cD
    cE
    c.mi
    co
    wceq
    cB
    cC
    c.mi
    co
    cE
    cF
    c.mi
    co
    wceq
    cC
    cA
    c.mi
    co
    cF
    cD
    c.mi
    co
    wceq
    trgcgr.1
    trgcgr.2
    trgcgr.3
    wph
    cA
    cB
    cC
    cD
    cP
    c.sm
    cE
    cF
    cG
    c.mi
    trgcgrg.p
    trgcgrg.m
    trgcgrg.r
    trgcgrg.g
    trgcgrg.a
    trgcgrg.b
    trgcgrg.c
    trgcgrg.d
    trgcgrg.e
    trgcgrg.f
    trgcgrg
    mpbir3and
end
