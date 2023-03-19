include "ccarsg.mm"
include "cfv.mm"
include "cuni.mm"
include "wss.mm"
include "wcel.mm"
include "wceq.mm"
include "cv.mm"
include "wral.mm"
include "wa.mm"
include "cpw.mm"
include "carsgcl.mm"
include "sselda.mm"
include "elpwid.mm"
include "ralrimiva.mm"
include "unissb.mm"
include "sylibr.mm"
include "baselcarsg.mm"
include "unissel.mm"
include "syl2anc.mm"

theorem carsguni
  let wph: wff ph
  let cM: class M
  let cO: class O
  let cV: class V
  let va: setvar a
  let ve: setvar e
  let vm: setvar m
  let cA: class A
  assume carsgval.1: |- ( ph -> O e. V )
  assume carsgval.2: |- ( ph -> M : ~P O --> ( 0 [,] +oo ) )
  assume baselcarsg.1: |- ( ph -> ( M ` (/) ) = 0 )


  assert |- ( ph -> U. ( toCaraSiga ` M ) = O )

  proof
    wph
    cM
    ccarsg
    cfv
    #
    cuni
    #
    cO
    wss
    #
    cO
    @0
    wcel
    @1
    cO
    wceq
    wph
    va
    cv
    #
    cO
    wss
    #
    va
    @0
    wral
    @2
    wph
    @4
    va
    @0
    wph
    @3
    @0
    wcel
    wa
    @3
    cO
    wph
    @0
    cO
    cpw
    @3
    wph
    cM
    cO
    cV
    carsgval.1
    carsgval.2
    carsgcl
    sselda
    elpwid
    ralrimiva
    va
    @0
    cO
    unissb
    sylibr
    wph
    cM
    cO
    cV
    carsgval.1
    carsgval.2
    baselcarsg.1
    baselcarsg
    @0
    cO
    unissel
    syl2anc
end
