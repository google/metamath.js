include "crn.mm"
include "cuni.mm"
include "cstrkg.mm"
include "wcel.mm"
include "wss.mm"
include "tglnunirn.mm"
include "syl.mm"
include "elssuni.mm"
include "sseldd.mm"

theorem tglnpt
  let wph: wff ph
  let cA: class A
  let cP: class P
  let cG: class G
  let cI: class I
  let cL: class L
  let cX: class X
  let vf: setvar f
  let vi: setvar i
  let vp: setvar p
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume tglng.p: |- P = ( Base ` G )
  assume tglng.l: |- L = ( LineG ` G )
  assume tglng.i: |- I = ( Itv ` G )
  assume tglnpt.g: |- ( ph -> G e. TarskiG )
  assume tglnpt.a: |- ( ph -> A e. ran L )
  assume tglnpt.x: |- ( ph -> X e. A )


  assert |- ( ph -> X e. P )

  proof
    wph
    cL
    crn
    #
    cuni
    #
    cP
    cX
    wph
    cG
    cstrkg
    wcel
    @1
    cP
    wss
    tglnpt.g
    cP
    cG
    cI
    cL
    tglng.p
    tglng.l
    tglng.i
    tglnunirn
    syl
    wph
    cA
    @1
    cX
    wph
    cA
    @0
    wcel
    cA
    @1
    wss
    tglnpt.a
    cA
    @0
    elssuni
    syl
    tglnpt.x
    sseldd
    sseldd
end
