include "cv.mm"
include "co.mm"
include "wcel.mm"
include "wceq.mm"
include "wa.mm"
include "simpllr.mm"
include "simprd.mm"
include "cstrkg.mm"
include "ad4antr.mm"
include "simp-4r.mm"
include "simpld.mm"
include "tgbtwncom.mm"
include "simpr.mm"
include "simplr.mm"
include "tgbtwnexch2.mm"
include "tgbtwntriv1.mm"
include "tgcgrcomlr.mm"
include "eqcomd.mm"
include "tgcgrsub.mm"
include "axtgcgrid.mm"
include "oveq2d.mm"
include "eleqtrd.mm"
include "tgbtwnswapid.mm"
include "eqtrd.mm"
include "wrex.mm"
include "wbr.mm"
include "legov2.mm"
include "mpbid.mm"
include "ad2antrr.mm"
include "r19.29a.mm"
include "legov.mm"

theorem legtri3
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cP: class P
  let cG: class G
  let cI: class I
  let c.le: class .<_
  let c.mi: class .-
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cE: class E
  let cF: class F
  assume legval.p: |- P = ( Base ` G )
  assume legval.d: |- .- = ( dist ` G )
  assume legval.i: |- I = ( Itv ` G )
  assume legval.l: |- .<_ = ( leG ` G )
  assume legval.g: |- ( ph -> G e. TarskiG )
  assume legid.a: |- ( ph -> A e. P )
  assume legid.b: |- ( ph -> B e. P )
  assume legtrd.c: |- ( ph -> C e. P )
  assume legtrd.d: |- ( ph -> D e. P )
  assume legtri3.1: |- ( ph -> ( A .- B ) .<_ ( C .- D ) )
  assume legtri3.2: |- ( ph -> ( C .- D ) .<_ ( A .- B ) )


  assert |- ( ph -> ( A .- B ) = ( C .- D ) )

  proof
    wph
    vx
    cv
    #
    cC
    cD
    cI
    co
    wcel
    #
    cA
    cB
    c.mi
    co
    #
    cC
    @0
    c.mi
    co
    #
    wceq
    #
    wa
    #
    @2
    cC
    cD
    c.mi
    co
    #
    wceq
    #
    vx
    cP
    wph
    @0
    cP
    wcel
    #
    wa
    #
    @5
    wa
    #
    cD
    cC
    vy
    cv
    #
    cI
    co
    #
    wcel
    #
    cC
    @11
    c.mi
    co
    @2
    wceq
    #
    wa
    #
    @7
    vy
    cP
    @10
    @11
    cP
    wcel
    #
    wa
    #
    @15
    wa
    #
    @2
    @3
    @6
    @18
    @1
    @4
    @9
    @5
    @16
    @15
    simpllr
    #
    simprd
    #
    @18
    @0
    cD
    cC
    c.mi
    @18
    @0
    cD
    cC
    cP
    cG
    cI
    c.mi
    legval.p
    legval.d
    legval.i
    wph
    cG
    cstrkg
    wcel
    @8
    @5
    @16
    @15
    legval.g
    ad4antr
    #
    wph
    @8
    @5
    @16
    @15
    simp-4r
    #
    wph
    cD
    cP
    wcel
    @8
    @5
    @16
    @15
    legtrd.d
    ad4antr
    #
    wph
    cC
    cP
    wcel
    @8
    @5
    @16
    @15
    legtrd.c
    ad4antr
    #
    @18
    cC
    @0
    cD
    cP
    cG
    cI
    c.mi
    legval.p
    legval.d
    legval.i
    @21
    @24
    @22
    @23
    @18
    @1
    @4
    @19
    simpld
    tgbtwncom
    #
    @18
    cC
    cD
    @0
    cP
    cG
    cI
    c.mi
    legval.p
    legval.d
    legval.i
    @21
    @24
    @23
    @22
    @18
    cD
    @12
    cC
    @0
    cI
    co
    @18
    @13
    @14
    @17
    @15
    simpr
    #
    simpld
    #
    @18
    @11
    @0
    cC
    cI
    @18
    cP
    cG
    cI
    c.mi
    @11
    @0
    cB
    legval.p
    legval.d
    legval.i
    @21
    @10
    @16
    @15
    simplr
    #
    @22
    wph
    cB
    cP
    wcel
    @8
    @5
    @16
    @15
    legid.b
    ad4antr
    #
    @18
    @11
    @0
    cC
    cB
    cP
    cB
    cA
    cG
    cI
    c.mi
    legval.p
    legval.d
    legval.i
    @21
    @28
    @22
    @24
    @29
    @29
    wph
    cA
    cP
    wcel
    @8
    @5
    @16
    @15
    legid.a
    ad4antr
    #
    @18
    @11
    cD
    @0
    cC
    cP
    cG
    cI
    c.mi
    legval.p
    legval.d
    legval.i
    @21
    @28
    @23
    @22
    @24
    @18
    cC
    cD
    @11
    cP
    cG
    cI
    c.mi
    legval.p
    legval.d
    legval.i
    @21
    @24
    @23
    @28
    @27
    tgbtwncom
    @25
    tgbtwnexch2
    @18
    cB
    cA
    cP
    cG
    cI
    c.mi
    legval.p
    legval.d
    legval.i
    @21
    @29
    @30
    tgbtwntriv1
    @18
    cC
    @11
    cA
    cB
    cP
    cG
    cI
    c.mi
    legval.p
    legval.d
    legval.i
    @21
    @24
    @28
    @30
    @29
    @18
    @13
    @14
    @26
    simprd
    tgcgrcomlr
    @18
    cC
    @0
    cA
    cB
    cP
    cG
    cI
    c.mi
    legval.p
    legval.d
    legval.i
    @21
    @24
    @22
    @30
    @29
    @18
    @2
    @3
    @20
    eqcomd
    tgcgrcomlr
    tgcgrsub
    axtgcgrid
    oveq2d
    eleqtrd
    tgbtwncom
    tgbtwnswapid
    oveq2d
    eqtrd
    wph
    @15
    vy
    cP
    wrex
    #
    @8
    @5
    wph
    @6
    @2
    c.le
    wbr
    @31
    legtri3.2
    wph
    vy
    cC
    cD
    cA
    cB
    cP
    cG
    cI
    c.le
    c.mi
    legval.p
    legval.d
    legval.i
    legval.l
    legval.g
    legtrd.c
    legtrd.d
    legid.a
    legid.b
    legov2
    mpbid
    ad2antrr
    r19.29a
    wph
    @2
    @6
    c.le
    wbr
    @5
    vx
    cP
    wrex
    legtri3.1
    wph
    vx
    cA
    cB
    cC
    cD
    cP
    cG
    cI
    c.le
    c.mi
    legval.p
    legval.d
    legval.i
    legval.l
    legval.g
    legid.a
    legid.b
    legtrd.c
    legtrd.d
    legov
    mpbid
    r19.29a
end
