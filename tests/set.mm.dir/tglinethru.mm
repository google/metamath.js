include "cv.mm"
include "co.mm"
include "wceq.mm"
include "wne.mm"
include "wa.mm"
include "wcel.mm"
include "cstrkg.mm"
include "ad4antr.mm"
include "simp-4r.mm"
include "simpllr.mm"
include "simplrr.mm"
include "necomd.mm"
include "simpr.mm"
include "neeqtrd.mm"
include "simplrl.mm"
include "eleqtrd.mm"
include "tglineelsb2.mm"
include "oveq1d.mm"
include "3eqtr4d.mm"
include "tglinecom.mm"
include "3eqtrd.mm"
include "eqtrd.mm"
include "pm2.61dane.mm"
include "tgisline.mm"
include "r19.29vva.mm"

theorem tglinethru
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cP: class P
  let cQ: class Q
  let cG: class G
  let cI: class I
  let cL: class L
  let vx: setvar x
  let vy: setvar y
  assume tglineelsb2.p: |- B = ( Base ` G )
  assume tglineelsb2.i: |- I = ( Itv ` G )
  assume tglineelsb2.l: |- L = ( LineG ` G )
  assume tglineelsb2.g: |- ( ph -> G e. TarskiG )
  assume tglineelsb2.1: |- ( ph -> P e. B )
  assume tglineelsb2.2: |- ( ph -> Q e. B )
  assume tglineelsb2.4: |- ( ph -> P =/= Q )
  assume tglinethru.0: |- ( ph -> P =/= Q )
  assume tglinethru.1: |- ( ph -> A e. ran L )
  assume tglinethru.2: |- ( ph -> P e. A )
  assume tglinethru.3: |- ( ph -> Q e. A )


  assert |- ( ph -> A = ( P L Q ) )

  proof
    wph
    cA
    vx
    cv
    #
    vy
    cv
    #
    cL
    co
    #
    wceq
    #
    @0
    @1
    wne
    #
    wa
    #
    cA
    cP
    cQ
    cL
    co
    #
    wceq
    #
    vx
    vy
    cB
    cB
    wph
    @0
    cB
    wcel
    #
    wa
    #
    @1
    cB
    wcel
    #
    wa
    #
    @5
    wa
    #
    @7
    cP
    @0
    @12
    cP
    @0
    wceq
    #
    wa
    #
    @2
    @0
    cQ
    cL
    co
    cA
    @6
    @14
    cB
    @0
    @1
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
    @8
    @10
    @5
    @13
    tglineelsb2.g
    ad4antr
    wph
    @8
    @10
    @5
    @13
    simp-4r
    @9
    @10
    @5
    @13
    simpllr
    @11
    @3
    @4
    @13
    simplrr
    wph
    cQ
    cB
    wcel
    #
    @8
    @10
    @5
    @13
    tglineelsb2.2
    ad4antr
    @14
    cQ
    cP
    @0
    @14
    cP
    cQ
    wph
    cP
    cQ
    wne
    #
    @8
    @10
    @5
    @13
    tglinethru.0
    ad4antr
    necomd
    @12
    @13
    simpr
    #
    neeqtrd
    @14
    cQ
    cA
    @2
    wph
    cQ
    cA
    wcel
    #
    @8
    @10
    @5
    @13
    tglinethru.3
    ad4antr
    @11
    @3
    @4
    @13
    simplrl
    #
    eleqtrd
    tglineelsb2
    @20
    @14
    cP
    @0
    cQ
    cL
    @18
    oveq1d
    3eqtr4d
    @12
    cP
    @0
    wne
    #
    wa
    #
    cA
    cP
    @0
    cL
    co
    #
    @6
    @22
    cA
    @2
    @0
    cP
    cL
    co
    @23
    @11
    @3
    @4
    @21
    simplrl
    #
    @22
    cB
    @0
    @1
    cP
    cG
    cI
    cL
    tglineelsb2.p
    tglineelsb2.i
    tglineelsb2.l
    wph
    @15
    @8
    @10
    @5
    @21
    tglineelsb2.g
    ad4antr
    #
    wph
    @8
    @10
    @5
    @21
    simp-4r
    #
    @9
    @10
    @5
    @21
    simpllr
    @11
    @3
    @4
    @21
    simplrr
    wph
    cP
    cB
    wcel
    @8
    @10
    @5
    @21
    tglineelsb2.1
    ad4antr
    #
    @12
    @21
    simpr
    #
    @22
    cP
    cA
    @2
    wph
    cP
    cA
    wcel
    @8
    @10
    @5
    @21
    tglinethru.2
    ad4antr
    @24
    eleqtrd
    tglineelsb2
    @22
    cB
    @0
    cP
    cG
    cI
    cL
    tglineelsb2.p
    tglineelsb2.i
    tglineelsb2.l
    @25
    @26
    @27
    @22
    cP
    @0
    @28
    necomd
    tglinecom
    3eqtrd
    #
    @22
    cB
    cP
    @0
    cQ
    cG
    cI
    cL
    tglineelsb2.p
    tglineelsb2.i
    tglineelsb2.l
    @25
    @27
    @26
    @28
    wph
    @16
    @8
    @10
    @5
    @21
    tglineelsb2.2
    ad4antr
    @22
    cP
    cQ
    wph
    @17
    @8
    @10
    @5
    @21
    tglinethru.0
    ad4antr
    necomd
    @22
    cQ
    cA
    @23
    wph
    @19
    @8
    @10
    @5
    @21
    tglinethru.3
    ad4antr
    @29
    eleqtrd
    tglineelsb2
    eqtrd
    pm2.61dane
    wph
    vx
    vy
    cA
    cB
    cG
    cI
    cL
    tglineelsb2.p
    tglineelsb2.i
    tglineelsb2.l
    tglineelsb2.g
    tglinethru.1
    tgisline
    r19.29vva
end
