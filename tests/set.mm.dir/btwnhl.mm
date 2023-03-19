include "co.mm"
include "wcel.mm"
include "wa.mm"
include "cds.mm"
include "cfv.mm"
include "eqid.mm"
include "cstrkg.mm"
include "adantr.mm"
include "wne.mm"
include "wo.mm"
include "wbr.mm"
include "w3a.mm"
include "ishlg.mm"
include "mpbid.mm"
include "simp1d.mm"
include "necomd.mm"
include "tgbtwncom.mm"
include "simpr.mm"
include "tgbtwnouttr.mm"
include "tgbtwnexch3.mm"
include "simp3d.mm"
include "mpjaodan.mm"

theorem btwnhl
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cP: class P
  let cG: class G
  let cI: class I
  let cK: class K
  assume ishlg.p: |- P = ( Base ` G )
  assume ishlg.i: |- I = ( Itv ` G )
  assume ishlg.k: |- K = ( hlG ` G )
  assume ishlg.a: |- ( ph -> A e. P )
  assume ishlg.b: |- ( ph -> B e. P )
  assume ishlg.c: |- ( ph -> C e. P )
  assume hlln.1: |- ( ph -> G e. TarskiG )
  assume hltr.d: |- ( ph -> D e. P )
  assume btwnhl.1: |- ( ph -> A ( K ` D ) B )
  assume btwnhl.3: |- ( ph -> D e. ( A I C ) )


  assert |- ( ph -> D e. ( B I C ) )

  proof
    wph
    cA
    cD
    cB
    cI
    co
    wcel
    #
    cD
    cB
    cC
    cI
    co
    wcel
    cB
    cD
    cA
    cI
    co
    wcel
    #
    wph
    @0
    wa
    #
    cC
    cD
    cB
    cP
    cG
    cI
    cG
    cds
    cfv
    #
    ishlg.p
    @3
    eqid
    #
    ishlg.i
    wph
    cG
    cstrkg
    wcel
    #
    @0
    hlln.1
    adantr
    #
    wph
    cC
    cP
    wcel
    #
    @0
    ishlg.c
    adantr
    #
    wph
    cD
    cP
    wcel
    #
    @0
    hltr.d
    adantr
    #
    wph
    cB
    cP
    wcel
    #
    @0
    ishlg.b
    adantr
    #
    @2
    cC
    cD
    cA
    cB
    cP
    cG
    cI
    @3
    ishlg.p
    @4
    ishlg.i
    @6
    @8
    @10
    wph
    cA
    cP
    wcel
    #
    @0
    ishlg.a
    adantr
    #
    @12
    wph
    cD
    cA
    wne
    @0
    wph
    cA
    cD
    wph
    cA
    cD
    wne
    #
    cB
    cD
    wne
    #
    @0
    @1
    wo
    #
    wph
    cA
    cB
    cD
    cK
    cfv
    wbr
    @15
    @16
    @17
    w3a
    btwnhl.1
    wph
    cA
    cB
    cD
    cP
    cG
    cI
    cK
    cstrkg
    ishlg.p
    ishlg.i
    ishlg.k
    ishlg.a
    ishlg.b
    hltr.d
    hlln.1
    ishlg
    mpbid
    #
    simp1d
    necomd
    adantr
    @2
    cA
    cD
    cC
    cP
    cG
    cI
    @3
    ishlg.p
    @4
    ishlg.i
    @6
    @14
    @10
    @8
    wph
    cD
    cA
    cC
    cI
    co
    wcel
    #
    @0
    btwnhl.3
    adantr
    tgbtwncom
    wph
    @0
    simpr
    tgbtwnouttr
    tgbtwncom
    wph
    @1
    wa
    #
    cA
    cB
    cD
    cC
    cP
    cG
    cI
    @3
    ishlg.p
    @4
    ishlg.i
    wph
    @5
    @1
    hlln.1
    adantr
    #
    wph
    @13
    @1
    ishlg.a
    adantr
    #
    wph
    @11
    @1
    ishlg.b
    adantr
    #
    wph
    @9
    @1
    hltr.d
    adantr
    #
    wph
    @7
    @1
    ishlg.c
    adantr
    @20
    cD
    cB
    cA
    cP
    cG
    cI
    @3
    ishlg.p
    @4
    ishlg.i
    @21
    @24
    @23
    @22
    wph
    @1
    simpr
    tgbtwncom
    wph
    @19
    @1
    btwnhl.3
    adantr
    tgbtwnexch3
    wph
    @15
    @16
    @17
    @18
    simp3d
    mpjaodan
end
