include "cv.mm"
include "co.mm"
include "wceq.mm"
include "wne.mm"
include "wa.mm"
include "wrex.mm"
include "wcel.mm"
include "cstrkg.mm"
include "ad4antr.mm"
include "simp-4r.mm"
include "simpllr.mm"
include "simplrr.mm"
include "tglinerflx2.mm"
include "simplrl.mm"
include "eleqtrrd.mm"
include "simpr.mm"
include "eqnetrd.mm"
include "neeq2.mm"
include "rspcev.mm"
include "syl2anc.mm"
include "tglinerflx1.mm"
include "pm2.61dane.mm"
include "tgisline.mm"
include "r19.29vva.mm"

theorem tglnpt2
  let wph: wff ph
  let vy: setvar y
  let cA: class A
  let cP: class P
  let cG: class G
  let cI: class I
  let cL: class L
  let cX: class X
  let vx: setvar x
  let vz: setvar z
  assume tglnpt2.p: |- P = ( Base ` G )
  assume tglnpt2.i: |- I = ( Itv ` G )
  assume tglnpt2.l: |- L = ( LineG ` G )
  assume tglnpt2.g: |- ( ph -> G e. TarskiG )
  assume tglnpt2.a: |- ( ph -> A e. ran L )
  assume tglnpt2.x: |- ( ph -> X e. A )

  disjoint A y
  disjoint X y
  disjoint x y
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A z
  disjoint G x
  disjoint G z
  disjoint I x
  disjoint I z
  disjoint P x
  disjoint P z
  disjoint X x
  disjoint X z
  disjoint ph x
  disjoint ph z
  assert |- ( ph -> E. y e. A X =/= y )

  proof
    wph
    cA
    vx
    cv
    #
    vz
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
    cX
    vy
    cv
    #
    wne
    #
    vy
    cA
    wrex
    #
    vx
    vz
    cP
    cP
    wph
    @0
    cP
    wcel
    #
    wa
    #
    @1
    cP
    wcel
    #
    wa
    #
    @5
    wa
    #
    @8
    cX
    @0
    @13
    cX
    @0
    wceq
    #
    wa
    #
    @1
    cA
    wcel
    cX
    @1
    wne
    #
    @8
    @15
    @1
    @2
    cA
    @15
    cP
    @0
    @1
    cG
    cI
    cL
    tglnpt2.p
    tglnpt2.i
    tglnpt2.l
    wph
    cG
    cstrkg
    wcel
    #
    @9
    @11
    @5
    @14
    tglnpt2.g
    ad4antr
    wph
    @9
    @11
    @5
    @14
    simp-4r
    @10
    @11
    @5
    @14
    simpllr
    @12
    @3
    @4
    @14
    simplrr
    #
    tglinerflx2
    @12
    @3
    @4
    @14
    simplrl
    eleqtrrd
    @15
    cX
    @0
    @1
    @13
    @14
    simpr
    @18
    eqnetrd
    @7
    @16
    vy
    @1
    cA
    @6
    @1
    cX
    neeq2
    rspcev
    syl2anc
    @13
    cX
    @0
    wne
    #
    wa
    #
    @0
    cA
    wcel
    @19
    @8
    @20
    @0
    @2
    cA
    @20
    cP
    @0
    @1
    cG
    cI
    cL
    tglnpt2.p
    tglnpt2.i
    tglnpt2.l
    wph
    @17
    @9
    @11
    @5
    @19
    tglnpt2.g
    ad4antr
    wph
    @9
    @11
    @5
    @19
    simp-4r
    @10
    @11
    @5
    @19
    simpllr
    @12
    @3
    @4
    @19
    simplrr
    tglinerflx1
    @12
    @3
    @4
    @19
    simplrl
    eleqtrrd
    @13
    @19
    simpr
    @7
    @19
    vy
    @0
    cA
    @6
    @0
    cX
    neeq2
    rspcev
    syl2anc
    pm2.61dane
    wph
    vx
    vz
    cA
    cP
    cG
    cI
    cL
    tglnpt2.p
    tglnpt2.i
    tglnpt2.l
    tglnpt2.g
    tglnpt2.a
    tgisline
    r19.29vva
end
