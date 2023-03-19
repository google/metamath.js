include "cwsuc.mm"
include "ccnv.mm"
include "cpred.mm"
include "cinf.mm"
include "df-wsuc.mm"
include "wwe.mm"
include "wor.mm"
include "weso.mm"
include "syl.mm"
include "wsuclem.mm"
include "infcl.mm"
include "syl5eqel.mm"

theorem wsuccl
  let wph: wff ph
  let vy: setvar y
  let cA: class A
  let cR: class R
  let cV: class V
  let cX: class X
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  assume wsuccl.1: |- ( ph -> R We A )
  assume wsuccl.2: |- ( ph -> R Se A )
  assume wsuccl.3: |- ( ph -> X e. V )
  assume wsuccl.4: |- ( ph -> E. y e. A X R y )

  disjoint R y
  disjoint A y
  disjoint X y
  disjoint R a
  disjoint R b
  disjoint R c
  disjoint a b
  disjoint a c
  disjoint a y
  disjoint b c
  disjoint b y
  disjoint c y
  disjoint A a
  disjoint A b
  disjoint A c
  disjoint X a
  disjoint X b
  disjoint X c
  disjoint a ph
  disjoint b ph
  assert |- ( ph -> wsuc ( R , A , X ) e. A )

  proof
    wph
    cA
    cR
    cX
    cwsuc
    cA
    cR
    ccnv
    cX
    cpred
    #
    cA
    cR
    cinf
    cA
    cA
    cR
    cX
    df-wsuc
    wph
    va
    vb
    vc
    cA
    @0
    cR
    wph
    cA
    cR
    wwe
    cA
    cR
    wor
    wsuccl.1
    cA
    cR
    weso
    syl
    wph
    va
    vb
    vc
    vy
    cA
    cR
    cV
    cX
    wsuccl.1
    wsuccl.2
    wsuccl.3
    wsuccl.4
    wsuclem
    infcl
    syl5eqel
end
