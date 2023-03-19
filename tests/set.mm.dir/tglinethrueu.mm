include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "crn.mm"
include "wrex.mm"
include "wrmo.mm"
include "wreu.mm"
include "tghilberti1.mm"
include "tghilberti2.mm"
include "reu5.mm"
include "sylanbrc.mm"

theorem tglinethrueu
  let wph: wff ph
  let vx: setvar x
  let cB: class B
  let cP: class P
  let cQ: class Q
  let cG: class G
  let cI: class I
  let cL: class L
  let vy: setvar y
  assume tglineelsb2.p: |- B = ( Base ` G )
  assume tglineelsb2.i: |- I = ( Itv ` G )
  assume tglineelsb2.l: |- L = ( LineG ` G )
  assume tglineelsb2.g: |- ( ph -> G e. TarskiG )
  assume tglineelsb2.1: |- ( ph -> P e. B )
  assume tglineelsb2.2: |- ( ph -> Q e. B )
  assume tglineelsb2.4: |- ( ph -> P =/= Q )

  disjoint B x
  disjoint G x
  disjoint I x
  disjoint L x
  disjoint P x
  disjoint Q x
  disjoint ph x
  disjoint B y
  disjoint x y
  disjoint G y
  disjoint I y
  disjoint L y
  disjoint P y
  disjoint Q y
  disjoint ph y
  assert |- ( ph -> E! x e. ran L ( P e. x /\ Q e. x ) )

  proof
    wph
    cP
    vx
    cv
    #
    wcel
    cQ
    @0
    wcel
    wa
    #
    vx
    cL
    crn
    #
    wrex
    @1
    vx
    @2
    wrmo
    @1
    vx
    @2
    wreu
    wph
    vx
    cB
    cP
    cQ
    cG
    cI
    cL
    tglineelsb2.p
    tglineelsb2.i
    tglineelsb2.l
    tglineelsb2.g
    tglineelsb2.1
    tglineelsb2.2
    tglineelsb2.4
    tghilberti1
    wph
    vx
    cB
    cP
    cQ
    cG
    cI
    cL
    tglineelsb2.p
    tglineelsb2.i
    tglineelsb2.l
    tglineelsb2.g
    tglineelsb2.1
    tglineelsb2.2
    tglineelsb2.4
    tghilberti2
    @1
    vx
    @2
    reu5
    sylanbrc
end
