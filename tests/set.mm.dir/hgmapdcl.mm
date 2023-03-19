include "cfv.mm"
include "hgmapcl.mm"
include "lcdsbase.mm"
include "eleqtrrd.mm"

theorem hgmapdcl
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cQ: class Q
  let cR: class R
  let cU: class U
  let cF: class F
  let cG: class G
  let cH: class H
  let cK: class K
  let cW: class W
  assume hgmapdcl.h: |- H = ( LHyp ` K )
  assume hgmapdcl.u: |- U = ( ( DVecH ` K ) ` W )
  assume hgmapdcl.r: |- R = ( Scalar ` U )
  assume hgmapdcl.b: |- B = ( Base ` R )
  assume hgmapdcl.c: |- C = ( ( LCDual ` K ) ` W )
  assume hgmapdcl.q: |- Q = ( Scalar ` C )
  assume hgmapdcl.a: |- A = ( Base ` Q )
  assume hgmapdcl.g: |- G = ( ( HGMap ` K ) ` W )
  assume hgmapdcl.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume hgmapdcl.f: |- ( ph -> F e. B )


  assert |- ( ph -> ( G ` F ) e. A )

  proof
    wph
    cF
    cG
    cfv
    cB
    cA
    wph
    cB
    cR
    cU
    cF
    cG
    cH
    cK
    cW
    hgmapdcl.h
    hgmapdcl.u
    hgmapdcl.r
    hgmapdcl.b
    hgmapdcl.g
    hgmapdcl.k
    hgmapdcl.f
    hgmapcl
    wph
    cC
    cA
    cQ
    cU
    cR
    cH
    cK
    cB
    cW
    hgmapdcl.h
    hgmapdcl.u
    hgmapdcl.r
    hgmapdcl.b
    hgmapdcl.c
    hgmapdcl.q
    hgmapdcl.a
    hgmapdcl.k
    lcdsbase
    eleqtrrd
end
