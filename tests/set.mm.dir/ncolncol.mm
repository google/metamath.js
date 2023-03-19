include "co.mm"
include "wcel.mm"
include "wceq.mm"
include "wo.mm"
include "wa.mm"
include "cstrkg.mm"
include "adantr.mm"
include "ad2antrr.mm"
include "wne.mm"
include "tglngne.mm"
include "necomd.mm"
include "simpr.mm"
include "lncom.mm"
include "tglineelsb2.mm"
include "eleqtrrd.mm"
include "orcd.mm"
include "pm2.21ddne.mm"
include "colrot2.mm"
include "mpjaodan.mm"
include "colrot1.mm"
include "mtand.mm"

theorem ncolncol
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cP: class P
  let cG: class G
  let cI: class I
  let cL: class L
  let vx: setvar x
  let cX: class X
  let cY: class Y
  let vy: setvar y
  assume tglineintmo.p: |- P = ( Base ` G )
  assume tglineintmo.i: |- I = ( Itv ` G )
  assume tglineintmo.l: |- L = ( LineG ` G )
  assume tglineintmo.g: |- ( ph -> G e. TarskiG )
  assume tglineinteq.a: |- ( ph -> A e. P )
  assume tglineinteq.b: |- ( ph -> B e. P )
  assume tglineinteq.c: |- ( ph -> C e. P )
  assume tglineinteq.d: |- ( ph -> D e. P )
  assume tglineinteq.e: |- ( ph -> -. ( A e. ( B L C ) \/ B = C ) )
  assume ncolncol.1: |- ( ph -> D e. ( A L B ) )
  assume ncolncol.2: |- ( ph -> D =/= B )


  assert |- ( ph -> -. ( D e. ( B L C ) \/ B = C ) )

  proof
    wph
    cD
    cB
    cC
    cL
    co
    #
    wcel
    cB
    cC
    wceq
    #
    wo
    #
    cA
    @0
    wcel
    @1
    wo
    tglineinteq.e
    wph
    @2
    wa
    #
    cP
    cG
    cI
    cL
    cA
    cB
    cC
    tglineintmo.p
    tglineintmo.l
    tglineintmo.i
    wph
    cG
    cstrkg
    wcel
    #
    @2
    tglineintmo.g
    adantr
    #
    wph
    cA
    cP
    wcel
    #
    @2
    tglineinteq.a
    adantr
    wph
    cB
    cP
    wcel
    #
    @2
    tglineinteq.b
    adantr
    #
    wph
    cC
    cP
    wcel
    #
    @2
    tglineinteq.c
    adantr
    #
    @3
    cC
    cD
    cB
    cL
    co
    wcel
    #
    cC
    cA
    cB
    cL
    co
    wcel
    #
    cA
    cB
    wceq
    #
    wo
    #
    cD
    cB
    wceq
    #
    @3
    @11
    wa
    #
    @12
    @13
    @16
    cP
    cG
    cI
    cL
    cA
    cB
    cC
    tglineintmo.p
    tglineintmo.i
    tglineintmo.l
    wph
    @4
    @2
    @11
    tglineintmo.g
    ad2antrr
    #
    wph
    @6
    @2
    @11
    tglineinteq.a
    ad2antrr
    wph
    @7
    @2
    @11
    tglineinteq.b
    ad2antrr
    #
    wph
    @9
    @2
    @11
    tglineinteq.c
    ad2antrr
    #
    wph
    cA
    cB
    wne
    @2
    @11
    wph
    cP
    cG
    cI
    cL
    cA
    cB
    cD
    tglineintmo.p
    tglineintmo.l
    tglineintmo.i
    tglineintmo.g
    tglineinteq.a
    tglineinteq.b
    ncolncol.1
    tglngne
    #
    ad2antrr
    @16
    cC
    cB
    cD
    cL
    co
    #
    cB
    cA
    cL
    co
    #
    @16
    cP
    cG
    cI
    cL
    cB
    cD
    cC
    tglineintmo.p
    tglineintmo.i
    tglineintmo.l
    @17
    @18
    wph
    cD
    cP
    wcel
    #
    @2
    @11
    tglineinteq.d
    ad2antrr
    @19
    wph
    cB
    cD
    wne
    @2
    @11
    wph
    cD
    cB
    ncolncol.2
    necomd
    ad2antrr
    @3
    @11
    simpr
    lncom
    wph
    @22
    @21
    wceq
    @2
    @11
    wph
    cP
    cB
    cA
    cD
    cG
    cI
    cL
    tglineintmo.p
    tglineintmo.i
    tglineintmo.l
    tglineintmo.g
    tglineinteq.b
    tglineinteq.a
    wph
    cA
    cB
    @20
    necomd
    #
    tglineinteq.d
    ncolncol.2
    wph
    cP
    cG
    cI
    cL
    cB
    cA
    cD
    tglineintmo.p
    tglineintmo.i
    tglineintmo.l
    tglineintmo.g
    tglineinteq.b
    tglineinteq.a
    tglineinteq.d
    @24
    ncolncol.1
    lncom
    tglineelsb2
    ad2antrr
    eleqtrrd
    lncom
    orcd
    @3
    @15
    wa
    @14
    cD
    cB
    @3
    @15
    simpr
    wph
    cD
    cB
    wne
    @2
    @15
    ncolncol.2
    ad2antrr
    pm2.21ddne
    @3
    cP
    cG
    cI
    cL
    cB
    cC
    cD
    tglineintmo.p
    tglineintmo.l
    tglineintmo.i
    @5
    @8
    @10
    wph
    @23
    @2
    tglineinteq.d
    adantr
    wph
    @2
    simpr
    colrot2
    mpjaodan
    colrot1
    mtand
end
