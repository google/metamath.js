include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "crab.mm"
include "cress.mm"
include "co.mm"
include "lcdval.mm"
include "oveq2i.mm"
include "syl6eqr.mm"

theorem lcdval2
  let wph: wff ph
  let cB: class B
  let cC: class C
  let cD: class D
  let cU: class U
  let vf: setvar f
  let cF: class F
  let cH: class H
  let cK: class K
  let cL: class L
  let c.pe: class ._|_
  let cW: class W
  let cX: class X
  let vk: setvar k
  let vw: setvar w
  assume lcdval.h: |- H = ( LHyp ` K )
  assume lcdval.o: |- ._|_ = ( ( ocH ` K ) ` W )
  assume lcdval.c: |- C = ( ( LCDual ` K ) ` W )
  assume lcdval.u: |- U = ( ( DVecH ` K ) ` W )
  assume lcdval.f: |- F = ( LFnl ` U )
  assume lcdval.l: |- L = ( LKer ` U )
  assume lcdval.d: |- D = ( LDual ` U )
  assume lcdval.k: |- ( ph -> ( K e. X /\ W e. H ) )
  assume lcdval2.b: |- B = { f e. F | ( ._|_ ` ( ._|_ ` ( L ` f ) ) ) = ( L ` f ) }

  disjoint K f
  disjoint F f
  disjoint W f
  disjoint k w
  disjoint H k
  disjoint H w
  disjoint f k
  disjoint f w
  disjoint K k
  disjoint K w
  disjoint D w
  disjoint F w
  disjoint L w
  disjoint ._|_ w
  disjoint W w
  assert |- ( ph -> C = ( D |`s B ) )

  proof
    wph
    cC
    cD
    vf
    cv
    cL
    cfv
    #
    c.pe
    cfv
    c.pe
    cfv
    @0
    wceq
    vf
    cF
    crab
    #
    cress
    co
    cD
    cB
    cress
    co
    wph
    cC
    cD
    cU
    vf
    cF
    cH
    cK
    cL
    c.pe
    cW
    cX
    lcdval.h
    lcdval.o
    lcdval.c
    lcdval.u
    lcdval.f
    lcdval.l
    lcdval.d
    lcdval.k
    lcdval
    cB
    @1
    cD
    cress
    lcdval2.b
    oveq2i
    syl6eqr
end
