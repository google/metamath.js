include "co.mm"
include "wcel.mm"
include "simpr.mm"
include "wa.mm"
include "cstrkg.mm"
include "adantr.mm"
include "tgbtwncom.mm"
include "tgbtwntriv1.mm"
include "wbr.mm"
include "btwnleg.mm"
include "legtri3.mm"
include "tgcgrcomlr.mm"
include "eqidd.mm"
include "tgcgrsub.mm"
include "axtgcgrid.mm"
include "eqeltrd.mm"
include "oveq2d.mm"
include "eleqtrd.mm"
include "mpjaodan.mm"

theorem legbtwn
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
  assume legbtwn.1: |- ( ph -> ( A e. ( C I B ) \/ B e. ( C I A ) ) )
  assume legbtwn.2: |- ( ph -> ( C .- A ) .<_ ( C .- B ) )


  assert |- ( ph -> A e. ( C I B ) )

  proof
    wph
    cA
    cC
    cB
    cI
    co
    #
    wcel
    #
    @1
    cB
    cC
    cA
    cI
    co
    #
    wcel
    #
    wph
    @1
    simpr
    wph
    @3
    wa
    #
    cA
    @2
    @0
    @4
    cA
    cB
    @2
    @4
    cP
    cG
    cI
    c.mi
    cA
    cB
    cB
    legval.p
    legval.d
    legval.i
    wph
    cG
    cstrkg
    wcel
    @3
    legval.g
    adantr
    #
    wph
    cA
    cP
    wcel
    @3
    legid.a
    adantr
    #
    wph
    cB
    cP
    wcel
    @3
    legid.b
    adantr
    #
    @7
    @4
    cA
    cB
    cC
    cB
    cP
    cB
    cC
    cG
    cI
    c.mi
    legval.p
    legval.d
    legval.i
    @5
    @6
    @7
    wph
    cC
    cP
    wcel
    @3
    legtrd.c
    adantr
    #
    @7
    @7
    @8
    @4
    cC
    cB
    cA
    cP
    cG
    cI
    c.mi
    legval.p
    legval.d
    legval.i
    @5
    @8
    @7
    @6
    wph
    @3
    simpr
    #
    tgbtwncom
    @4
    cB
    cC
    cP
    cG
    cI
    c.mi
    legval.p
    legval.d
    legval.i
    @5
    @7
    @8
    tgbtwntriv1
    @4
    cC
    cA
    cC
    cB
    cP
    cG
    cI
    c.mi
    legval.p
    legval.d
    legval.i
    @5
    @8
    @6
    @8
    @7
    @4
    cC
    cA
    cC
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
    @5
    @8
    @6
    @8
    @7
    wph
    cC
    cA
    c.mi
    co
    cC
    cB
    c.mi
    co
    c.le
    wbr
    @3
    legbtwn.2
    adantr
    @4
    cC
    cB
    cA
    cP
    cG
    cI
    c.le
    c.mi
    legval.p
    legval.d
    legval.i
    legval.l
    @5
    @8
    @7
    @6
    @9
    btwnleg
    legtri3
    tgcgrcomlr
    @4
    cB
    cC
    c.mi
    co
    eqidd
    tgcgrsub
    axtgcgrid
    #
    @9
    eqeltrd
    @4
    cA
    cB
    cC
    cI
    @10
    oveq2d
    eleqtrd
    legbtwn.1
    mpjaodan
end
