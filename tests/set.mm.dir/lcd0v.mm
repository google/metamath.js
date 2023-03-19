include "cld.mm"
include "cfv.mm"
include "cv.mm"
include "clk.mm"
include "coch.mm"
include "wceq.mm"
include "clfn.mm"
include "crab.mm"
include "cress.mm"
include "co.mm"
include "c0g.mm"
include "csn.mm"
include "cxp.mm"
include "chlt.mm"
include "eqid.mm"
include "lcdval.mm"
include "fveq2d.mm"
include "syl5eq.mm"
include "clmod.mm"
include "wcel.mm"
include "clss.mm"
include "dvhlmod.mm"
include "lduallmod.mm"
include "lclkr.mm"
include "lss0v.mm"
include "syl2anc.mm"
include "ldual0v.mm"
include "3eqtrd.mm"

theorem lcd0v
  let wph: wff ph
  let cC: class C
  let cR: class R
  let cU: class U
  let cH: class H
  let cK: class K
  let cO: class O
  let cV: class V
  let cW: class W
  let c.0: class .0.
  let vf: setvar f
  assume lcd0v.h: |- H = ( LHyp ` K )
  assume lcd0v.u: |- U = ( ( DVecH ` K ) ` W )
  assume lcd0v.v: |- V = ( Base ` U )
  assume lcd0v.r: |- R = ( Scalar ` U )
  assume lcd0v.z: |- .0. = ( 0g ` R )
  assume lcd0v.c: |- C = ( ( LCDual ` K ) ` W )
  assume lcd0v.o: |- O = ( 0g ` C )
  assume lcd0v.k: |- ( ph -> ( K e. HL /\ W e. H ) )


  assert |- ( ph -> O = ( V X. { .0. } ) )

  proof
    wph
    cO
    cU
    cld
    cfv
    #
    vf
    cv
    cU
    clk
    cfv
    #
    cfv
    #
    cW
    cK
    coch
    cfv
    cfv
    #
    cfv
    @3
    cfv
    @2
    wceq
    vf
    cU
    clfn
    cfv
    #
    crab
    #
    cress
    co
    #
    c0g
    cfv
    #
    @0
    c0g
    cfv
    #
    cV
    c.0
    csn
    cxp
    wph
    cO
    cC
    c0g
    cfv
    @7
    lcd0v.o
    wph
    cC
    @6
    c0g
    wph
    cC
    @0
    cU
    vf
    @4
    cH
    cK
    @1
    @3
    cW
    chlt
    lcd0v.h
    @3
    eqid
    #
    lcd0v.c
    lcd0v.u
    @4
    eqid
    #
    @1
    eqid
    #
    @0
    eqid
    #
    lcd0v.k
    lcdval
    fveq2d
    syl5eq
    wph
    @0
    clmod
    wcel
    @5
    @0
    clss
    cfv
    #
    wcel
    @7
    @8
    wceq
    wph
    @0
    cU
    @12
    wph
    cU
    cH
    cK
    cW
    lcd0v.h
    lcd0v.u
    lcd0v.k
    dvhlmod
    #
    lduallmod
    wph
    @5
    @0
    @13
    cU
    vf
    @4
    cH
    cK
    @1
    @3
    cW
    lcd0v.h
    lcd0v.u
    @9
    @10
    @11
    @12
    @13
    eqid
    #
    @5
    eqid
    lcd0v.k
    lclkr
    @5
    @13
    @0
    @6
    @8
    @7
    @6
    eqid
    @8
    eqid
    #
    @7
    eqid
    @15
    lss0v
    syl2anc
    wph
    @0
    cR
    @8
    cV
    cU
    c.0
    lcd0v.v
    lcd0v.r
    lcd0v.z
    @12
    @16
    @14
    ldual0v
    3eqtrd
end
