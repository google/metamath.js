include "clvec.mm"
include "wcel.mm"
include "clmod.mm"
include "lcdlvec.mm"
include "lveclmod.mm"
include "syl.mm"

theorem lcdlmod
  let wph: wff ph
  let cC: class C
  let cH: class H
  let cK: class K
  let cW: class W
  let vf: setvar f
  assume lcdlmod.h: |- H = ( LHyp ` K )
  assume lcdlmod.c: |- C = ( ( LCDual ` K ) ` W )
  assume lcdlmod.k: |- ( ph -> ( K e. HL /\ W e. H ) )


  assert |- ( ph -> C e. LMod )

  proof
    wph
    cC
    clvec
    wcel
    cC
    clmod
    wcel
    wph
    cC
    cH
    cK
    cW
    lcdlmod.h
    lcdlmod.c
    lcdlmod.k
    lcdlvec
    cC
    lveclmod
    syl
end
