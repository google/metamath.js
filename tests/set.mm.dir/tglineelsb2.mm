include "co.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "cstrkg.mm"
include "adantr.mm"
include "wne.mm"
include "necomd.mm"
include "lncom.mm"
include "lnrot1.mm"
include "tglnssp.mm"
include "sselda.mm"
include "simpr.mm"
include "tglineeltr.mm"
include "impbida.mm"
include "eqrdv.mm"

theorem tglineelsb2
  let wph: wff ph
  let cB: class B
  let cP: class P
  let cQ: class Q
  let cS: class S
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
  assume tglineelsb2.3: |- ( ph -> S e. B )
  assume tglineelsb2.5: |- ( ph -> S =/= P )
  assume tglineelsb2.6: |- ( ph -> S e. ( P L Q ) )


  assert |- ( ph -> ( P L Q ) = ( P L S ) )

  proof
    wph
    vx
    cP
    cQ
    cL
    co
    #
    cP
    cS
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
    #
    cB
    cP
    cS
    @2
    cQ
    cG
    cI
    cL
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
    #
    wph
    cP
    cB
    wcel
    #
    @3
    tglineelsb2.1
    adantr
    #
    wph
    cS
    cB
    wcel
    #
    @3
    tglineelsb2.3
    adantr
    #
    wph
    cP
    cS
    wne
    @3
    wph
    cS
    cP
    tglineelsb2.5
    necomd
    #
    adantr
    #
    wph
    cQ
    cB
    wcel
    #
    @3
    tglineelsb2.2
    adantr
    #
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
    adantr
    #
    @5
    cB
    cG
    cI
    cL
    cP
    cS
    cQ
    tglineelsb2.p
    tglineelsb2.i
    tglineelsb2.l
    @7
    @9
    @11
    @15
    @13
    @5
    cB
    cG
    cI
    cL
    cQ
    cP
    cS
    tglineelsb2.p
    tglineelsb2.i
    tglineelsb2.l
    @7
    @15
    @9
    @11
    @16
    wph
    cS
    @0
    wcel
    #
    @3
    tglineelsb2.6
    adantr
    lncom
    @16
    lnrot1
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
    @3
    simpr
    tglineeltr
    wph
    @4
    wa
    cB
    cP
    cQ
    @2
    cS
    cG
    cI
    cL
    tglineelsb2.p
    tglineelsb2.i
    tglineelsb2.l
    wph
    @6
    @4
    tglineelsb2.g
    adantr
    wph
    @8
    @4
    tglineelsb2.1
    adantr
    wph
    @14
    @4
    tglineelsb2.2
    adantr
    wph
    cP
    cQ
    wne
    @4
    tglineelsb2.4
    adantr
    wph
    @10
    @4
    tglineelsb2.3
    adantr
    wph
    cS
    cP
    wne
    @4
    tglineelsb2.5
    adantr
    wph
    @17
    @4
    tglineelsb2.6
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
    cP
    cS
    tglineelsb2.p
    tglineelsb2.l
    tglineelsb2.i
    tglineelsb2.g
    tglineelsb2.1
    tglineelsb2.3
    @12
    tglnssp
    sselda
    wph
    @4
    simpr
    tglineeltr
    impbida
    eqrdv
end
