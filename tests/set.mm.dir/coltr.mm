include "co.mm"
include "wcel.mm"
include "wceq.mm"
include "wo.mm"
include "wa.mm"
include "wne.mm"
include "cstrkg.mm"
include "adantr.mm"
include "simpr.mm"
include "tglinerflx1.mm"
include "ex.mm"
include "necon1bd.mm"
include "orrd.mm"
include "simplr.mm"
include "eqeltrd.mm"
include "orim1d.mm"
include "mpd.mm"
include "wn.mm"
include "ad2antrr.mm"
include "tglngne.mm"
include "necomd.mm"
include "lncom.mm"
include "lnrot2.mm"
include "ncolncol.mm"
include "condan.mm"
include "pm2.61dane.mm"

theorem coltr
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
  let vy: setvar y
  assume tglineintmo.p: |- P = ( Base ` G )
  assume tglineintmo.i: |- I = ( Itv ` G )
  assume tglineintmo.l: |- L = ( LineG ` G )
  assume tglineintmo.g: |- ( ph -> G e. TarskiG )
  assume coltr.a: |- ( ph -> A e. P )
  assume coltr.b: |- ( ph -> B e. P )
  assume coltr.c: |- ( ph -> C e. P )
  assume coltr.d: |- ( ph -> D e. P )
  assume coltr.1: |- ( ph -> A e. ( B L C ) )
  assume coltr.2: |- ( ph -> ( B e. ( C L D ) \/ C = D ) )


  assert |- ( ph -> ( A e. ( C L D ) \/ C = D ) )

  proof
    wph
    cA
    cC
    cD
    cL
    co
    #
    wcel
    #
    cC
    cD
    wceq
    #
    wo
    #
    cA
    cC
    wph
    cA
    cC
    wceq
    #
    wa
    #
    cC
    @0
    wcel
    #
    @2
    wo
    #
    @3
    wph
    @7
    @4
    wph
    @6
    @2
    wph
    @6
    cC
    cD
    wph
    cC
    cD
    wne
    #
    @6
    wph
    @8
    wa
    cP
    cC
    cD
    cG
    cI
    cL
    tglineintmo.p
    tglineintmo.i
    tglineintmo.l
    wph
    cG
    cstrkg
    wcel
    #
    @8
    tglineintmo.g
    adantr
    wph
    cC
    cP
    wcel
    #
    @8
    coltr.c
    adantr
    wph
    cD
    cP
    wcel
    #
    @8
    coltr.d
    adantr
    wph
    @8
    simpr
    tglinerflx1
    ex
    necon1bd
    orrd
    adantr
    @5
    @6
    @1
    @2
    @5
    @6
    @1
    @5
    @6
    wa
    cA
    cC
    @0
    wph
    @4
    @6
    simplr
    @5
    @6
    simpr
    eqeltrd
    ex
    orim1d
    mpd
    wph
    cA
    cC
    wne
    #
    wa
    #
    @3
    cB
    @0
    wcel
    @2
    wo
    #
    wph
    @14
    @12
    @3
    wn
    #
    coltr.2
    ad2antrr
    @13
    @15
    wa
    cA
    cC
    cD
    cB
    cP
    cG
    cI
    cL
    tglineintmo.p
    tglineintmo.i
    tglineintmo.l
    wph
    @9
    @12
    @15
    tglineintmo.g
    ad2antrr
    wph
    cA
    cP
    wcel
    #
    @12
    @15
    coltr.a
    ad2antrr
    wph
    @10
    @12
    @15
    coltr.c
    ad2antrr
    wph
    @11
    @12
    @15
    coltr.d
    ad2antrr
    wph
    cB
    cP
    wcel
    #
    @12
    @15
    coltr.b
    ad2antrr
    @13
    @15
    simpr
    @13
    cB
    cA
    cC
    cL
    co
    wcel
    @15
    @13
    cP
    cG
    cI
    cL
    cA
    cC
    cB
    tglineintmo.p
    tglineintmo.i
    tglineintmo.l
    wph
    @9
    @12
    tglineintmo.g
    adantr
    #
    wph
    @16
    @12
    coltr.a
    adantr
    #
    wph
    @10
    @12
    coltr.c
    adantr
    #
    wph
    @17
    @12
    coltr.b
    adantr
    #
    wph
    @12
    simpr
    @13
    cP
    cG
    cI
    cL
    cC
    cB
    cA
    tglineintmo.p
    tglineintmo.i
    tglineintmo.l
    @18
    @20
    @21
    @19
    @13
    cB
    cC
    @13
    cP
    cG
    cI
    cL
    cB
    cC
    cA
    tglineintmo.p
    tglineintmo.l
    tglineintmo.i
    @18
    @21
    @20
    wph
    cA
    cB
    cC
    cL
    co
    wcel
    @12
    coltr.1
    adantr
    #
    tglngne
    necomd
    #
    @22
    lncom
    @23
    lnrot2
    adantr
    wph
    cB
    cC
    wne
    @12
    @15
    wph
    cP
    cG
    cI
    cL
    cB
    cC
    cA
    tglineintmo.p
    tglineintmo.l
    tglineintmo.i
    tglineintmo.g
    coltr.b
    coltr.c
    coltr.1
    tglngne
    ad2antrr
    ncolncol
    condan
    pm2.61dane
end
