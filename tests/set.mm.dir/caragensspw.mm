include "cdm.mm"
include "cuni.mm"
include "cpw.mm"
include "come.mm"
include "wcel.mm"
include "wss.mm"
include "caragenss.mm"
include "syl.mm"
include "pwuni.mm"
include "a1i.mm"
include "sstrd.mm"
include "wceq.mm"
include "pweqi.mm"
include "eqcomi.mm"
include "sseqtrd.mm"

theorem caragensspw
  let wph: wff ph
  let cS: class S
  let cO: class O
  let cX: class X
  let vk: setvar k
  let vx: setvar x
  assume caragensspw.o: |- ( ph -> O e. OutMeas )
  assume caragensspw.x: |- X = U. dom O
  assume caragensspw.s: |- S = ( CaraGen ` O )


  assert |- ( ph -> S C_ ~P X )

  proof
    wph
    cS
    cO
    cdm
    #
    cuni
    #
    cpw
    #
    cX
    cpw
    #
    wph
    cS
    @0
    @2
    wph
    cO
    come
    wcel
    cS
    @0
    wss
    caragensspw.o
    cS
    cO
    caragensspw.s
    caragenss
    syl
    @0
    @2
    wss
    wph
    @0
    pwuni
    a1i
    sstrd
    @2
    @3
    wceq
    wph
    @3
    @2
    cX
    @1
    caragensspw.x
    pweqi
    eqcomi
    a1i
    sseqtrd
end
