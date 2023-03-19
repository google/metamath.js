include "co.mm"
include "wcel.mm"
include "wo.mm"
include "wa.mm"
include "cds.mm"
include "cfv.mm"
include "eqid.mm"
include "cstrkg.mm"
include "adantr.mm"
include "simpr.mm"
include "tgbtwnexch3.mm"
include "orcd.mm"
include "olcd.mm"
include "tgbtwnconn1.mm"
include "mpjaodan.mm"

theorem tgbtwnconn2
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cP: class P
  let cG: class G
  let cI: class I
  assume tgbtwnconn.p: |- P = ( Base ` G )
  assume tgbtwnconn.i: |- I = ( Itv ` G )
  assume tgbtwnconn.g: |- ( ph -> G e. TarskiG )
  assume tgbtwnconn.a: |- ( ph -> A e. P )
  assume tgbtwnconn.b: |- ( ph -> B e. P )
  assume tgbtwnconn.c: |- ( ph -> C e. P )
  assume tgbtwnconn.d: |- ( ph -> D e. P )
  assume tgbtwnconn2.1: |- ( ph -> A =/= B )
  assume tgbtwnconn2.2: |- ( ph -> B e. ( A I C ) )
  assume tgbtwnconn2.3: |- ( ph -> B e. ( A I D ) )


  assert |- ( ph -> ( C e. ( B I D ) \/ D e. ( B I C ) ) )

  proof
    wph
    cC
    cA
    cD
    cI
    co
    #
    wcel
    #
    cC
    cB
    cD
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
    #
    wo
    cD
    cA
    cC
    cI
    co
    #
    wcel
    #
    wph
    @1
    wa
    #
    @2
    @3
    @6
    cA
    cB
    cC
    cD
    cP
    cG
    cI
    cG
    cds
    cfv
    #
    tgbtwnconn.p
    @7
    eqid
    #
    tgbtwnconn.i
    wph
    cG
    cstrkg
    wcel
    #
    @1
    tgbtwnconn.g
    adantr
    wph
    cA
    cP
    wcel
    #
    @1
    tgbtwnconn.a
    adantr
    wph
    cB
    cP
    wcel
    #
    @1
    tgbtwnconn.b
    adantr
    wph
    cC
    cP
    wcel
    #
    @1
    tgbtwnconn.c
    adantr
    wph
    cD
    cP
    wcel
    #
    @1
    tgbtwnconn.d
    adantr
    wph
    cB
    @4
    wcel
    @1
    tgbtwnconn2.2
    adantr
    wph
    @1
    simpr
    tgbtwnexch3
    orcd
    wph
    @5
    wa
    #
    @3
    @2
    @14
    cA
    cB
    cD
    cC
    cP
    cG
    cI
    @7
    tgbtwnconn.p
    @8
    tgbtwnconn.i
    wph
    @9
    @5
    tgbtwnconn.g
    adantr
    wph
    @10
    @5
    tgbtwnconn.a
    adantr
    wph
    @11
    @5
    tgbtwnconn.b
    adantr
    wph
    @13
    @5
    tgbtwnconn.d
    adantr
    wph
    @12
    @5
    tgbtwnconn.c
    adantr
    wph
    cB
    @0
    wcel
    @5
    tgbtwnconn2.3
    adantr
    wph
    @5
    simpr
    tgbtwnexch3
    olcd
    wph
    cA
    cB
    cC
    cD
    cP
    cG
    cI
    tgbtwnconn.p
    tgbtwnconn.i
    tgbtwnconn.g
    tgbtwnconn.a
    tgbtwnconn.b
    tgbtwnconn.c
    tgbtwnconn.d
    tgbtwnconn2.1
    tgbtwnconn2.2
    tgbtwnconn2.3
    tgbtwnconn1
    mpjaodan
end
