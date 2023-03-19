include "clmod.mm"
include "wcel.mm"
include "lcdlmod.mm"
include "lmod0vcl.mm"
include "syl.mm"

theorem lcd0vcl
  let wph: wff ph
  let cC: class C
  let cH: class H
  let cK: class K
  let cO: class O
  let cV: class V
  let cW: class W
  assume lcdv0cl.h: |- H = ( LHyp ` K )
  assume lcdv0cl.c: |- C = ( ( LCDual ` K ) ` W )
  assume lcdv0cl.v: |- V = ( Base ` C )
  assume lcdv0cl.o: |- O = ( 0g ` C )
  assume lcdv0cl.k: |- ( ph -> ( K e. HL /\ W e. H ) )


  assert |- ( ph -> O e. V )

  proof
    wph
    cC
    clmod
    wcel
    cO
    cV
    wcel
    wph
    cC
    cH
    cK
    cW
    lcdv0cl.h
    lcdv0cl.c
    lcdv0cl.k
    lcdlmod
    cV
    cC
    cO
    lcdv0cl.v
    lcdv0cl.o
    lmod0vcl
    syl
end
