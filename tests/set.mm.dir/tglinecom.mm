include "co.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "cstrkg.mm"
include "adantr.mm"
include "tglnssp.mm"
include "sselda.mm"
include "wne.mm"
include "necomd.mm"
include "simpr.mm"
include "lncom.mm"
include "impbida.mm"
include "eqrdv.mm"

theorem tglinecom
  let wph: wff ph
  let cB: class B
  let cP: class P
  let cQ: class Q
  let cG: class G
  let cI: class I
  let cL: class L
  let vx: setvar x
  assume tglineelsb2.p: |- B = ( Base ` G )
  assume tglineelsb2.i: |- I = ( Itv ` G )
  assume tglineelsb2.l: |- L = ( LineG ` G )
  assume tglineelsb2.g: |- ( ph -> G e. TarskiG )
  assume tglineelsb2.1: |- ( ph -> P e. B )
  assume tglineelsb2.2: |- ( ph -> Q e. B )
  assume tglineelsb2.4: |- ( ph -> P =/= Q )


  assert |- ( ph -> ( P L Q ) = ( Q L P ) )

  proof
    wph
    vx
    cP
    cQ
    cL
    co
    #
    cQ
    cP
    cL
    co
    #
    wph
    vx
    cv
    #
    @0
    wcel
    #
    @2
    @1
    wcel
    #
    wph
    @3
    wa
    cB
    cG
    cI
    cL
    cQ
    cP
    @2
    tglineelsb2.p
    tglineelsb2.i
    tglineelsb2.l
    wph
    cG
    cstrkg
    wcel
    #
    @3
    tglineelsb2.g
    adantr
    wph
    cQ
    cB
    wcel
    #
    @3
    tglineelsb2.2
    adantr
    wph
    cP
    cB
    wcel
    #
    @3
    tglineelsb2.1
    adantr
    wph
    @0
    cB
    @2
    wph
    cB
    cG
    cI
    cL
    cP
    cQ
    tglineelsb2.p
    tglineelsb2.l
    tglineelsb2.i
    tglineelsb2.g
    tglineelsb2.1
    tglineelsb2.2
    tglineelsb2.4
    tglnssp
    sselda
    wph
    cQ
    cP
    wne
    @3
    wph
    cP
    cQ
    tglineelsb2.4
    necomd
    #
    adantr
    wph
    @3
    simpr
    lncom
    wph
    @4
    wa
    cB
    cG
    cI
    cL
    cP
    cQ
    @2
    tglineelsb2.p
    tglineelsb2.i
    tglineelsb2.l
    wph
    @5
    @4
    tglineelsb2.g
    adantr
    wph
    @7
    @4
    tglineelsb2.1
    adantr
    wph
    @6
    @4
    tglineelsb2.2
    adantr
    wph
    @1
    cB
    @2
    wph
    cB
    cG
    cI
    cL
    cQ
    cP
    tglineelsb2.p
    tglineelsb2.l
    tglineelsb2.i
    tglineelsb2.g
    tglineelsb2.2
    tglineelsb2.1
    @8
    tglnssp
    sselda
    wph
    cP
    cQ
    wne
    @4
    tglineelsb2.4
    adantr
    wph
    @4
    simpr
    lncom
    impbida
    eqrdv
end
