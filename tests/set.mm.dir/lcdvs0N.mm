include "clmod.mm"
include "wcel.mm"
include "csca.mm"
include "cfv.mm"
include "cbs.mm"
include "co.mm"
include "wceq.mm"
include "lcdlmod.mm"
include "eqid.mm"
include "lcdsbase.mm"
include "eleqtrrd.mm"
include "lmodvs0.mm"
include "syl2anc.mm"

theorem lcdvs0N
  let wph: wff ph
  let cC: class C
  let cR: class R
  let cS: class S
  let c.x: class .x.
  let cU: class U
  let cH: class H
  let cK: class K
  let cW: class W
  let cX: class X
  let c.0: class .0.
  assume lcdvs0.h: |- H = ( LHyp ` K )
  assume lcdvs0.u: |- U = ( ( DVecH ` K ) ` W )
  assume lcdvs0.s: |- S = ( Scalar ` U )
  assume lcdvs0.r: |- R = ( Base ` S )
  assume lcdvs0.c: |- C = ( ( LCDual ` K ) ` W )
  assume lcdvs0.t: |- .x. = ( .s ` C )
  assume lcdvs0.o: |- .0. = ( 0g ` C )
  assume lcdvs0.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume lcdvs0.x: |- ( ph -> X e. R )


  assert |- ( ph -> ( X .x. .0. ) = .0. )

  proof
    wph
    cC
    clmod
    wcel
    cX
    cC
    csca
    cfv
    #
    cbs
    cfv
    #
    wcel
    cX
    c.0
    c.x
    co
    c.0
    wceq
    wph
    cC
    cH
    cK
    cW
    lcdvs0.h
    lcdvs0.c
    lcdvs0.k
    lcdlmod
    wph
    cX
    cR
    @1
    lcdvs0.x
    wph
    cC
    @1
    @0
    cU
    cS
    cH
    cK
    cR
    cW
    lcdvs0.h
    lcdvs0.u
    lcdvs0.s
    lcdvs0.r
    lcdvs0.c
    @0
    eqid
    #
    @1
    eqid
    #
    lcdvs0.k
    lcdsbase
    eleqtrrd
    c.x
    @0
    @1
    cC
    cX
    c.0
    @2
    lcdvs0.t
    @3
    lcdvs0.o
    lmodvs0
    syl2anc
end
