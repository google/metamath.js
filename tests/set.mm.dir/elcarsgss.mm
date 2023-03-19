include "ccarsg.mm"
include "cfv.mm"
include "cpw.mm"
include "carsgcl.mm"
include "sseldd.mm"
include "elpwid.mm"

theorem elcarsgss
  let wph: wff ph
  let cA: class A
  let cM: class M
  let cO: class O
  let cV: class V
  let va: setvar a
  let ve: setvar e
  let vm: setvar m
  assume carsgval.1: |- ( ph -> O e. V )
  assume carsgval.2: |- ( ph -> M : ~P O --> ( 0 [,] +oo ) )
  assume difelcarsg.1: |- ( ph -> A e. ( toCaraSiga ` M ) )


  assert |- ( ph -> A C_ O )

  proof
    wph
    cA
    cO
    wph
    cM
    ccarsg
    cfv
    cO
    cpw
    cA
    wph
    cM
    cO
    cV
    carsgval.1
    carsgval.2
    carsgcl
    difelcarsg.1
    sseldd
    elpwid
end
