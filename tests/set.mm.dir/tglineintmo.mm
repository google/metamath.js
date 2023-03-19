include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "wceq.mm"
include "wi.mm"
include "wal.mm"
include "wmo.mm"
include "wne.mm"
include "wn.mm"
include "co.mm"
include "cstrkg.mm"
include "ad2antrr.mm"
include "wss.mm"
include "crn.mm"
include "cuni.mm"
include "elssuni.mm"
include "syl.mm"
include "tglnunirn.mm"
include "sstrd.mm"
include "simplrl.mm"
include "simpld.mm"
include "sseldd.mm"
include "simplrr.mm"
include "simpr.mm"
include "tglinethru.mm"
include "simprd.mm"
include "eqtr4d.mm"
include "neneqd.mm"
include "pm2.65da.mm"
include "nne.mm"
include "sylib.mm"
include "ex.mm"
include "alrimivv.mm"
include "eleq1.mm"
include "anbi12d.mm"
include "mo4.mm"
include "sylibr.mm"

theorem tglineintmo
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cP: class P
  let cG: class G
  let cI: class I
  let cL: class L
  let vy: setvar y
  assume tglineintmo.p: |- P = ( Base ` G )
  assume tglineintmo.i: |- I = ( Itv ` G )
  assume tglineintmo.l: |- L = ( LineG ` G )
  assume tglineintmo.g: |- ( ph -> G e. TarskiG )
  assume tglineintmo.a: |- ( ph -> A e. ran L )
  assume tglineintmo.b: |- ( ph -> B e. ran L )
  assume tglineintmo.c: |- ( ph -> A =/= B )

  disjoint A x
  disjoint B x
  disjoint ph x
  disjoint A y
  disjoint x y
  disjoint B y
  disjoint ph y
  assert |- ( ph -> E* x ( x e. A /\ x e. B ) )

  proof
    wph
    vx
    cv
    #
    cA
    wcel
    #
    @0
    cB
    wcel
    #
    wa
    #
    vy
    cv
    #
    cA
    wcel
    #
    @4
    cB
    wcel
    #
    wa
    #
    wa
    #
    @0
    @4
    wceq
    #
    wi
    #
    vy
    wal
    vx
    wal
    @3
    vx
    wmo
    wph
    @10
    vx
    vy
    wph
    @8
    @9
    wph
    @8
    wa
    #
    @0
    @4
    wne
    #
    wn
    @9
    @11
    @12
    cA
    cB
    wceq
    @11
    @12
    wa
    #
    cA
    @0
    @4
    cL
    co
    cB
    @13
    cA
    cP
    @0
    @4
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
    @12
    tglineintmo.g
    ad2antrr
    #
    @13
    cA
    cP
    @0
    wph
    cA
    cP
    wss
    @8
    @12
    wph
    cA
    cL
    crn
    #
    cuni
    #
    cP
    wph
    cA
    @16
    wcel
    #
    cA
    @17
    wss
    tglineintmo.a
    cA
    @16
    elssuni
    syl
    wph
    @14
    @17
    cP
    wss
    tglineintmo.g
    cP
    cG
    cI
    cL
    tglineintmo.p
    tglineintmo.l
    tglineintmo.i
    tglnunirn
    syl
    sstrd
    ad2antrr
    #
    @13
    @1
    @2
    wph
    @3
    @7
    @12
    simplrl
    #
    simpld
    #
    sseldd
    #
    @13
    cA
    cP
    @4
    @19
    @13
    @5
    @6
    wph
    @3
    @7
    @12
    simplrr
    #
    simpld
    #
    sseldd
    #
    @11
    @12
    simpr
    #
    @26
    wph
    @18
    @8
    @12
    tglineintmo.a
    ad2antrr
    @21
    @24
    tglinethru
    @13
    cB
    cP
    @0
    @4
    cG
    cI
    cL
    tglineintmo.p
    tglineintmo.i
    tglineintmo.l
    @15
    @22
    @25
    @26
    @26
    wph
    cB
    @16
    wcel
    @8
    @12
    tglineintmo.b
    ad2antrr
    @13
    @1
    @2
    @20
    simprd
    @13
    @5
    @6
    @23
    simprd
    tglinethru
    eqtr4d
    @13
    cA
    cB
    wph
    cA
    cB
    wne
    @8
    @12
    tglineintmo.c
    ad2antrr
    neneqd
    pm2.65da
    @0
    @4
    nne
    sylib
    ex
    alrimivv
    @3
    @7
    vx
    vy
    @9
    @1
    @5
    @2
    @6
    @0
    @4
    cA
    eleq1
    @0
    @4
    cB
    eleq1
    anbi12d
    mo4
    sylibr
end
