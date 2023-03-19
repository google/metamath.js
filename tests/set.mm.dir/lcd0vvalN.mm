include "cfv.mm"
include "csn.mm"
include "cxp.mm"
include "lcd0v.mm"
include "fveq1d.mm"
include "wcel.mm"
include "wceq.mm"
include "c0g.mm"
include "cvv.mm"
include "fvex.mm"
include "eqeltri.mm"
include "fvconst2.mm"
include "syl.mm"
include "eqtrd.mm"

theorem lcd0vvalN
  let wph: wff ph
  let cC: class C
  let cS: class S
  let cU: class U
  let cH: class H
  let cK: class K
  let cO: class O
  let cV: class V
  let cW: class W
  let cX: class X
  let c.0: class .0.
  assume lcd0vval.h: |- H = ( LHyp ` K )
  assume lcd0vval.u: |- U = ( ( DVecH ` K ) ` W )
  assume lcd0vval.v: |- V = ( Base ` U )
  assume lcd0vval.s: |- S = ( Scalar ` U )
  assume lcd0vval.z: |- .0. = ( 0g ` S )
  assume lcd0vval.c: |- C = ( ( LCDual ` K ) ` W )
  assume lcd0vval.o: |- O = ( 0g ` C )
  assume lcd0vval.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume lcd0vval.x: |- ( ph -> X e. V )


  assert |- ( ph -> ( O ` X ) = .0. )

  proof
    wph
    cX
    cO
    cfv
    cX
    cV
    c.0
    csn
    cxp
    #
    cfv
    #
    c.0
    wph
    cX
    cO
    @0
    wph
    cC
    cS
    cU
    cH
    cK
    cO
    cV
    cW
    c.0
    lcd0vval.h
    lcd0vval.u
    lcd0vval.v
    lcd0vval.s
    lcd0vval.z
    lcd0vval.c
    lcd0vval.o
    lcd0vval.k
    lcd0v
    fveq1d
    wph
    cX
    cV
    wcel
    @1
    c.0
    wceq
    lcd0vval.x
    cV
    c.0
    cX
    c.0
    cS
    c0g
    cfv
    cvv
    lcd0vval.z
    cS
    c0g
    fvex
    eqeltri
    fvconst2
    syl
    eqtrd
end
