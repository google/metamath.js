include "clss.mm"
include "cfv.mm"
include "wcel.mm"
include "wss.mm"
include "eqid.mm"
include "lsatlssel.mm"
include "lssss.mm"
include "syl.mm"

theorem lsatssv
  let wph: wff ph
  let cA: class A
  let cQ: class Q
  let cV: class V
  let cW: class W
  assume lsatssv.v: |- V = ( Base ` W )
  assume lsatssv.a: |- A = ( LSAtoms ` W )
  assume lsatssv.w: |- ( ph -> W e. LMod )
  assume lsatssv.g: |- ( ph -> Q e. A )


  assert |- ( ph -> Q C_ V )

  proof
    wph
    cQ
    cW
    clss
    cfv
    #
    wcel
    cQ
    cV
    wss
    wph
    cA
    @0
    cQ
    cW
    @0
    eqid
    #
    lsatssv.a
    lsatssv.w
    lsatssv.g
    lsatlssel
    @0
    cQ
    cV
    cW
    lsatssv.v
    @1
    lssss
    syl
end
