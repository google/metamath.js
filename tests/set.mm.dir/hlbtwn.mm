include "wne.mm"
include "co.mm"
include "wcel.mm"
include "wo.mm"
include "w3a.mm"
include "cfv.mm"
include "wbr.mm"
include "2thd.mm"
include "wa.mm"
include "cstrkg.mm"
include "adantr.mm"
include "simpr.mm"
include "tgbtwnconn3.mm"
include "cds.mm"
include "eqid.mm"
include "tgbtwnexch.mm"
include "olcd.mm"
include "jaodan.mm"
include "orcd.mm"
include "necomd.mm"
include "tgbtwnconn1.mm"
include "impbida.mm"
include "3anbi23d.mm"
include "ishlg.mm"
include "3bitr4d.mm"

theorem hlbtwn
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
  assume hlbtwn.1: |- ( ph -> D e. ( C I B ) )
  assume hlbtwn.2: |- ( ph -> B =/= C )
  assume hlbtwn.3: |- ( ph -> D =/= C )


  assert |- ( ph -> ( A ( K ` C ) B <-> A ( K ` C ) D ) )

  proof
    wph
    cA
    cC
    wne
    #
    cB
    cC
    wne
    #
    cA
    cC
    cB
    cI
    co
    #
    wcel
    #
    cB
    cC
    cA
    cI
    co
    #
    wcel
    #
    wo
    #
    w3a
    @0
    cD
    cC
    wne
    #
    cA
    cC
    cD
    cI
    co
    wcel
    #
    cD
    @4
    wcel
    #
    wo
    #
    w3a
    cA
    cB
    cC
    cK
    cfv
    #
    wbr
    cA
    cD
    @11
    wbr
    wph
    @1
    @7
    @6
    @10
    @0
    wph
    @1
    @7
    hlbtwn.2
    hlbtwn.3
    2thd
    wph
    @6
    @10
    wph
    @3
    @10
    @5
    wph
    @3
    wa
    cC
    cA
    cD
    cB
    cP
    cG
    cI
    ishlg.p
    ishlg.i
    wph
    cG
    cstrkg
    wcel
    #
    @3
    hlln.1
    adantr
    wph
    cC
    cP
    wcel
    #
    @3
    ishlg.c
    adantr
    wph
    cA
    cP
    wcel
    #
    @3
    ishlg.a
    adantr
    wph
    cD
    cP
    wcel
    #
    @3
    hltr.d
    adantr
    wph
    cB
    cP
    wcel
    #
    @3
    ishlg.b
    adantr
    wph
    @3
    simpr
    wph
    cD
    @2
    wcel
    #
    @3
    hlbtwn.1
    adantr
    tgbtwnconn3
    wph
    @5
    wa
    #
    @9
    @8
    @18
    cC
    cD
    cB
    cA
    cP
    cG
    cI
    cG
    cds
    cfv
    #
    ishlg.p
    @19
    eqid
    #
    ishlg.i
    wph
    @12
    @5
    hlln.1
    adantr
    wph
    @13
    @5
    ishlg.c
    adantr
    wph
    @15
    @5
    hltr.d
    adantr
    wph
    @16
    @5
    ishlg.b
    adantr
    wph
    @14
    @5
    ishlg.a
    adantr
    wph
    @17
    @5
    hlbtwn.1
    adantr
    wph
    @5
    simpr
    tgbtwnexch
    olcd
    jaodan
    wph
    @8
    @6
    @9
    wph
    @8
    wa
    #
    @3
    @5
    @21
    cC
    cA
    cD
    cB
    cP
    cG
    cI
    @19
    ishlg.p
    @20
    ishlg.i
    wph
    @12
    @8
    hlln.1
    adantr
    wph
    @13
    @8
    ishlg.c
    adantr
    wph
    @14
    @8
    ishlg.a
    adantr
    wph
    @15
    @8
    hltr.d
    adantr
    wph
    @16
    @8
    ishlg.b
    adantr
    wph
    @8
    simpr
    wph
    @17
    @8
    hlbtwn.1
    adantr
    tgbtwnexch
    orcd
    wph
    @9
    wa
    cC
    cD
    cA
    cB
    cP
    cG
    cI
    ishlg.p
    ishlg.i
    wph
    @12
    @9
    hlln.1
    adantr
    wph
    @13
    @9
    ishlg.c
    adantr
    wph
    @15
    @9
    hltr.d
    adantr
    wph
    @14
    @9
    ishlg.a
    adantr
    wph
    @16
    @9
    ishlg.b
    adantr
    wph
    cC
    cD
    wne
    @9
    wph
    cD
    cC
    hlbtwn.3
    necomd
    adantr
    wph
    @9
    simpr
    wph
    @17
    @9
    hlbtwn.1
    adantr
    tgbtwnconn1
    jaodan
    impbida
    3anbi23d
    wph
    cA
    cB
    cC
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
    ishlg.c
    hlln.1
    ishlg
    wph
    cA
    cD
    cC
    cP
    cG
    cI
    cK
    cstrkg
    ishlg.p
    ishlg.i
    ishlg.k
    ishlg.a
    hltr.d
    ishlg.c
    hlln.1
    ishlg
    3bitr4d
end
