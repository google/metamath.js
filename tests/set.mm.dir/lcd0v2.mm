include "cbs.mm"
include "cfv.mm"
include "csca.mm"
include "c0g.mm"
include "csn.mm"
include "cxp.mm"
include "eqid.mm"
include "lcd0v.mm"
include "dvhlmod.mm"
include "ldual0v.mm"
include "eqtr4d.mm"

theorem lcd0v2
  let wph: wff ph
  let cC: class C
  let cD: class D
  let cU: class U
  let cH: class H
  let cK: class K
  let cO: class O
  let cW: class W
  let c.0: class .0.
  assume lcd0v2.h: |- H = ( LHyp ` K )
  assume lcd0v2.u: |- U = ( ( DVecH ` K ) ` W )
  assume lcd0v2.d: |- D = ( LDual ` U )
  assume lcd0v2.z: |- .0. = ( 0g ` D )
  assume lcd0v2.c: |- C = ( ( LCDual ` K ) ` W )
  assume lcd0v2.o: |- O = ( 0g ` C )
  assume lcd0v2.k: |- ( ph -> ( K e. HL /\ W e. H ) )


  assert |- ( ph -> O = .0. )

  proof
    wph
    cO
    cU
    cbs
    cfv
    #
    cU
    csca
    cfv
    #
    c0g
    cfv
    #
    csn
    cxp
    c.0
    wph
    cC
    @1
    cU
    cH
    cK
    cO
    @0
    cW
    @2
    lcd0v2.h
    lcd0v2.u
    @0
    eqid
    #
    @1
    eqid
    #
    @2
    eqid
    #
    lcd0v2.c
    lcd0v2.o
    lcd0v2.k
    lcd0v
    wph
    cD
    @1
    c.0
    @0
    cU
    @2
    @3
    @4
    @5
    lcd0v2.d
    lcd0v2.z
    wph
    cU
    cH
    cK
    cW
    lcd0v2.h
    lcd0v2.u
    lcd0v2.k
    dvhlmod
    ldual0v
    eqtr4d
end
