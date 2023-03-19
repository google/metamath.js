include "co.mm"
include "coppc.mm"
include "cfv.mm"
include "cmon.mm"
include "chomf.mm"
include "wceq.mm"
include "2oppchomf.mm"
include "a1i.mm"
include "ccomf.mm"
include "2oppccomf.mm"
include "ccat.mm"
include "wcel.mm"
include "oppccat.mm"
include "syl.mm"
include "eqid.mm"
include "monpropd.mm"
include "syl5eq.mm"
include "oveqd.mm"
include "oppcmon.mm"
include "eqtr2d.mm"

theorem oppcepi
  let wph: wff ph
  let cC: class C
  let cE: class E
  let cM: class M
  let cO: class O
  let cX: class X
  let cY: class Y
  let vc: setvar c
  assume oppcmon.o: |- O = ( oppCat ` C )
  assume oppcmon.c: |- ( ph -> C e. Cat )
  assume oppcepi.e: |- E = ( Epi ` O )
  assume oppcepi.m: |- M = ( Mono ` C )


  assert |- ( ph -> ( X E Y ) = ( Y M X ) )

  proof
    wph
    cY
    cX
    cM
    co
    cY
    cX
    cO
    coppc
    cfv
    #
    cmon
    cfv
    #
    co
    cX
    cY
    cE
    co
    wph
    cM
    @1
    cY
    cX
    wph
    cM
    cC
    cmon
    cfv
    @1
    oppcepi.m
    wph
    cC
    @0
    cC
    chomf
    cfv
    @0
    chomf
    cfv
    wceq
    wph
    cC
    cO
    oppcmon.o
    2oppchomf
    a1i
    cC
    ccomf
    cfv
    @0
    ccomf
    cfv
    wceq
    wph
    cC
    cO
    oppcmon.o
    2oppccomf
    a1i
    oppcmon.c
    wph
    cO
    ccat
    wcel
    #
    @0
    ccat
    wcel
    wph
    cC
    ccat
    wcel
    @2
    oppcmon.c
    cC
    cO
    oppcmon.o
    oppccat
    syl
    #
    cO
    @0
    @0
    eqid
    #
    oppccat
    syl
    monpropd
    syl5eq
    oveqd
    wph
    cO
    cE
    @1
    @0
    cY
    cX
    @4
    @3
    @1
    eqid
    oppcepi.e
    oppcmon
    eqtr2d
end
