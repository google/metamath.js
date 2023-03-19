include "co.mm"
include "wcel.mm"
include "cfv.mm"
include "wceq.mm"
include "lcfl1lem.mm"
include "simplbi.mm"
include "syl.mm"
include "lcfl1.mm"
include "mpbid.mm"
include "lclkrlem2y.mm"
include "dvhlmod.mm"
include "ldualvaddcl.mm"
include "mpbird.mm"

theorem lclkrlem2
  let wph: wff ph
  let cC: class C
  let cD: class D
  let c.pl: class .+
  let cU: class U
  let vf: setvar f
  let cE: class E
  let cF: class F
  let cG: class G
  let cH: class H
  let cK: class K
  let cL: class L
  let c.pe: class ._|_
  let cW: class W
  assume lclkrlem2.h: |- H = ( LHyp ` K )
  assume lclkrlem2.o: |- ._|_ = ( ( ocH ` K ) ` W )
  assume lclkrlem2.u: |- U = ( ( DVecH ` K ) ` W )
  assume lclkrlem2.f: |- F = ( LFnl ` U )
  assume lclkrlem2.l: |- L = ( LKer ` U )
  assume lclkrlem2.d: |- D = ( LDual ` U )
  assume lclkrlem2.p: |- .+ = ( +g ` D )
  assume lclkrlem2.c: |- C = { f e. F | ( ._|_ ` ( ._|_ ` ( L ` f ) ) ) = ( L ` f ) }
  assume lclkrlem2.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume lclkrlem2.e: |- ( ph -> E e. C )
  assume lclkrlem2.g: |- ( ph -> G e. C )

  disjoint E f
  disjoint F f
  disjoint G f
  disjoint L f
  disjoint ._|_ f
  disjoint .+ f
  assert |- ( ph -> ( E .+ G ) e. C )

  proof
    wph
    cE
    cG
    c.pl
    co
    #
    cC
    wcel
    @0
    cL
    cfv
    #
    c.pe
    cfv
    c.pe
    cfv
    @1
    wceq
    wph
    cD
    c.pl
    cU
    cE
    cF
    cG
    cH
    cK
    cL
    c.pe
    cW
    lclkrlem2.l
    lclkrlem2.h
    lclkrlem2.o
    lclkrlem2.u
    lclkrlem2.f
    lclkrlem2.d
    lclkrlem2.p
    lclkrlem2.k
    wph
    cE
    cC
    wcel
    #
    cE
    cF
    wcel
    #
    lclkrlem2.e
    @2
    @3
    cE
    cL
    cfv
    #
    c.pe
    cfv
    c.pe
    cfv
    @4
    wceq
    #
    cC
    vf
    cF
    cE
    cL
    c.pe
    lclkrlem2.c
    lcfl1lem
    simplbi
    syl
    #
    wph
    cG
    cC
    wcel
    #
    cG
    cF
    wcel
    #
    lclkrlem2.g
    @7
    @8
    cG
    cL
    cfv
    #
    c.pe
    cfv
    c.pe
    cfv
    @9
    wceq
    #
    cC
    vf
    cF
    cG
    cL
    c.pe
    lclkrlem2.c
    lcfl1lem
    simplbi
    syl
    #
    wph
    @2
    @5
    lclkrlem2.e
    wph
    cC
    vf
    cF
    cE
    cL
    c.pe
    lclkrlem2.c
    @6
    lcfl1
    mpbid
    wph
    @7
    @10
    lclkrlem2.g
    wph
    cC
    vf
    cF
    cG
    cL
    c.pe
    lclkrlem2.c
    @11
    lcfl1
    mpbid
    lclkrlem2y
    wph
    cC
    vf
    cF
    @0
    cL
    c.pe
    lclkrlem2.c
    wph
    cD
    c.pl
    cF
    cE
    cG
    cU
    lclkrlem2.f
    lclkrlem2.d
    lclkrlem2.p
    wph
    cU
    cH
    cK
    cW
    lclkrlem2.h
    lclkrlem2.u
    lclkrlem2.k
    dvhlmod
    @6
    @11
    ldualvaddcl
    lcfl1
    mpbird
end
