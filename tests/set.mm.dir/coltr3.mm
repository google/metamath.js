include "co.mm"
include "wcel.mm"
include "wceq.mm"
include "wa.mm"
include "cds.mm"
include "cfv.mm"
include "eqid.mm"
include "cstrkg.mm"
include "adantr.mm"
include "simpr.mm"
include "oveq2d.mm"
include "eleqtrrd.mm"
include "axtgbtwnid.mm"
include "eqeltrrd.mm"
include "wne.mm"
include "btwnlng1.mm"
include "necomd.mm"
include "tglngne.mm"
include "lnrot1.mm"
include "tglineelsb2.mm"
include "tglinecom.mm"
include "3eqtr4d.mm"
include "eleqtrd.mm"
include "pm2.61dane.mm"

theorem coltr3
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
  assume coltr3.2: |- ( ph -> D e. ( A I C ) )


  assert |- ( ph -> D e. ( B L C ) )

  proof
    wph
    cD
    cB
    cC
    cL
    co
    #
    wcel
    cA
    cC
    wph
    cA
    cC
    wceq
    #
    wa
    #
    cA
    cD
    @0
    @2
    cP
    cG
    cI
    cG
    cds
    cfv
    #
    cA
    cD
    tglineintmo.p
    @3
    eqid
    tglineintmo.i
    wph
    cG
    cstrkg
    wcel
    #
    @1
    tglineintmo.g
    adantr
    wph
    cA
    cP
    wcel
    #
    @1
    coltr.a
    adantr
    wph
    cD
    cP
    wcel
    #
    @1
    coltr.d
    adantr
    @2
    cD
    cA
    cC
    cI
    co
    #
    cA
    cA
    cI
    co
    wph
    cD
    @7
    wcel
    #
    @1
    coltr3.2
    adantr
    @2
    cA
    cC
    cA
    cI
    wph
    @1
    simpr
    oveq2d
    eleqtrrd
    axtgbtwnid
    wph
    cA
    @0
    wcel
    #
    @1
    coltr.1
    adantr
    eqeltrrd
    wph
    cA
    cC
    wne
    #
    wa
    #
    cD
    cA
    cC
    cL
    co
    #
    @0
    @11
    cP
    cG
    cI
    cL
    cA
    cC
    cD
    tglineintmo.p
    tglineintmo.i
    tglineintmo.l
    wph
    @4
    @10
    tglineintmo.g
    adantr
    #
    wph
    @5
    @10
    coltr.a
    adantr
    #
    wph
    cC
    cP
    wcel
    @10
    coltr.c
    adantr
    #
    wph
    @6
    @10
    coltr.d
    adantr
    wph
    @10
    simpr
    #
    wph
    @8
    @10
    coltr3.2
    adantr
    btwnlng1
    @11
    cC
    cA
    cL
    co
    cC
    cB
    cL
    co
    #
    @12
    @0
    @11
    cP
    cC
    cA
    cB
    cG
    cI
    cL
    tglineintmo.p
    tglineintmo.i
    tglineintmo.l
    @13
    @15
    @14
    @11
    cA
    cC
    @16
    necomd
    #
    wph
    cB
    cP
    wcel
    @10
    coltr.b
    adantr
    #
    wph
    cB
    cC
    wne
    @10
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
    #
    adantr
    #
    @11
    cP
    cG
    cI
    cL
    cC
    cA
    cB
    tglineintmo.p
    tglineintmo.i
    tglineintmo.l
    @13
    @15
    @14
    @19
    @18
    wph
    @9
    @10
    coltr.1
    adantr
    @21
    lnrot1
    tglineelsb2
    @11
    cP
    cA
    cC
    cG
    cI
    cL
    tglineintmo.p
    tglineintmo.i
    tglineintmo.l
    @13
    @14
    @15
    @16
    tglinecom
    wph
    @0
    @17
    wceq
    @10
    wph
    cP
    cB
    cC
    cG
    cI
    cL
    tglineintmo.p
    tglineintmo.i
    tglineintmo.l
    tglineintmo.g
    coltr.b
    coltr.c
    @20
    tglinecom
    adantr
    3eqtr4d
    eleqtrd
    pm2.61dane
end
