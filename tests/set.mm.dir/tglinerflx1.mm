include "cds.mm"
include "cfv.mm"
include "eqid.mm"
include "tgbtwntriv1.mm"
include "btwnlng1.mm"

theorem tglinerflx1
  let wph: wff ph
  let cB: class B
  let cP: class P
  let cQ: class Q
  let cG: class G
  let cI: class I
  let cL: class L
  assume tglineelsb2.p: |- B = ( Base ` G )
  assume tglineelsb2.i: |- I = ( Itv ` G )
  assume tglineelsb2.l: |- L = ( LineG ` G )
  assume tglineelsb2.g: |- ( ph -> G e. TarskiG )
  assume tglineelsb2.1: |- ( ph -> P e. B )
  assume tglineelsb2.2: |- ( ph -> Q e. B )
  assume tglineelsb2.4: |- ( ph -> P =/= Q )


  assert |- ( ph -> P e. ( P L Q ) )

  proof
    wph
    cB
    cG
    cI
    cL
    cP
    cQ
    cP
    tglineelsb2.p
    tglineelsb2.i
    tglineelsb2.l
    tglineelsb2.g
    tglineelsb2.1
    tglineelsb2.2
    tglineelsb2.1
    tglineelsb2.4
    wph
    cP
    cQ
    cB
    cG
    cI
    cG
    cds
    cfv
    #
    tglineelsb2.p
    @0
    eqid
    tglineelsb2.i
    tglineelsb2.g
    tglineelsb2.1
    tglineelsb2.2
    tgbtwntriv1
    btwnlng1
end
