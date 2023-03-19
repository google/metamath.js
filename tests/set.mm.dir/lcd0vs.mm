include "csca.mm"
include "cfv.mm"
include "c0g.mm"
include "co.mm"
include "eqid.mm"
include "lcd0.mm"
include "oveq1d.mm"
include "clmod.mm"
include "wcel.mm"
include "wceq.mm"
include "lcdlmod.mm"
include "lmod0vs.mm"
include "syl2anc.mm"
include "eqtr3d.mm"

theorem lcd0vs
  let wph: wff ph
  let cC: class C
  let cR: class R
  let c.x: class .x.
  let cU: class U
  let cG: class G
  let cH: class H
  let cK: class K
  let cO: class O
  let cV: class V
  let cW: class W
  let c.0: class .0.
  assume lcd0vs.h: |- H = ( LHyp ` K )
  assume lcd0vs.u: |- U = ( ( DVecH ` K ) ` W )
  assume lcd0vs.r: |- R = ( Scalar ` U )
  assume lcd0vs.z: |- .0. = ( 0g ` R )
  assume lcd0vs.c: |- C = ( ( LCDual ` K ) ` W )
  assume lcd0vs.v: |- V = ( Base ` C )
  assume lcd0vs.t: |- .x. = ( .s ` C )
  assume lcd0vs.o: |- O = ( 0g ` C )
  assume lcd0vs.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume lcd0vs.g: |- ( ph -> G e. V )


  assert |- ( ph -> ( .0. .x. G ) = O )

  proof
    wph
    cC
    csca
    cfv
    #
    c0g
    cfv
    #
    cG
    c.x
    co
    #
    c.0
    cG
    c.x
    co
    cO
    wph
    @1
    c.0
    cG
    c.x
    wph
    cC
    @0
    cU
    cR
    cH
    cK
    @1
    cW
    c.0
    lcd0vs.h
    lcd0vs.u
    lcd0vs.r
    lcd0vs.z
    lcd0vs.c
    @0
    eqid
    #
    @1
    eqid
    #
    lcd0vs.k
    lcd0
    oveq1d
    wph
    cC
    clmod
    wcel
    cG
    cV
    wcel
    @2
    cO
    wceq
    wph
    cC
    cH
    cK
    cW
    lcd0vs.h
    lcd0vs.c
    lcd0vs.k
    lcdlmod
    lcd0vs.g
    c.x
    @0
    @1
    cV
    cC
    cG
    cO
    lcd0vs.v
    @3
    lcd0vs.t
    @4
    lcd0vs.o
    lmod0vs
    syl2anc
    eqtr3d
end
