include "co.mm"
include "wcel.mm"
include "wa.mm"
include "cds.mm"
include "cfv.mm"
include "eqid.mm"
include "cstrkg.mm"
include "adantr.mm"
include "wne.mm"
include "simpr.mm"
include "tgbtwncom.mm"
include "tgbtwnouttr2.mm"
include "tgbtwnintr.mm"
include "tgbtwnconn2.mm"
include "mpjaodan.mm"

theorem tgbtwnconn22
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cP: class P
  let cE: class E
  let cG: class G
  let cI: class I
  assume tgbtwnconn.p: |- P = ( Base ` G )
  assume tgbtwnconn.i: |- I = ( Itv ` G )
  assume tgbtwnconn.g: |- ( ph -> G e. TarskiG )
  assume tgbtwnconn.a: |- ( ph -> A e. P )
  assume tgbtwnconn.b: |- ( ph -> B e. P )
  assume tgbtwnconn.c: |- ( ph -> C e. P )
  assume tgbtwnconn.d: |- ( ph -> D e. P )
  assume tgbtwnconn22.e: |- ( ph -> E e. P )
  assume tgbtwnconn22.1: |- ( ph -> A =/= B )
  assume tgbtwnconn22.2: |- ( ph -> C =/= B )
  assume tgbtwnconn22.3: |- ( ph -> B e. ( A I C ) )
  assume tgbtwnconn22.4: |- ( ph -> B e. ( A I D ) )
  assume tgbtwnconn22.5: |- ( ph -> B e. ( C I E ) )


  assert |- ( ph -> B e. ( D I E ) )

  proof
    wph
    cC
    cB
    cD
    cI
    co
    wcel
    #
    cB
    cD
    cE
    cI
    co
    wcel
    cD
    cB
    cC
    cI
    co
    wcel
    #
    wph
    @0
    wa
    #
    cD
    cC
    cB
    cE
    cP
    cG
    cI
    cG
    cds
    cfv
    #
    tgbtwnconn.p
    @3
    eqid
    #
    tgbtwnconn.i
    wph
    cG
    cstrkg
    wcel
    #
    @0
    tgbtwnconn.g
    adantr
    #
    wph
    cD
    cP
    wcel
    #
    @0
    tgbtwnconn.d
    adantr
    #
    wph
    cC
    cP
    wcel
    #
    @0
    tgbtwnconn.c
    adantr
    #
    wph
    cB
    cP
    wcel
    #
    @0
    tgbtwnconn.b
    adantr
    #
    wph
    cE
    cP
    wcel
    #
    @0
    tgbtwnconn22.e
    adantr
    wph
    cC
    cB
    wne
    @0
    tgbtwnconn22.2
    adantr
    @2
    cB
    cC
    cD
    cP
    cG
    cI
    @3
    tgbtwnconn.p
    @4
    tgbtwnconn.i
    @6
    @12
    @10
    @8
    wph
    @0
    simpr
    tgbtwncom
    wph
    cB
    cC
    cE
    cI
    co
    wcel
    #
    @0
    tgbtwnconn22.5
    adantr
    tgbtwnouttr2
    wph
    @1
    wa
    #
    cD
    cB
    cE
    cC
    cP
    cG
    cI
    @3
    tgbtwnconn.p
    @4
    tgbtwnconn.i
    wph
    @5
    @1
    tgbtwnconn.g
    adantr
    #
    wph
    @7
    @1
    tgbtwnconn.d
    adantr
    wph
    @11
    @1
    tgbtwnconn.b
    adantr
    #
    wph
    @13
    @1
    tgbtwnconn22.e
    adantr
    #
    wph
    @9
    @1
    tgbtwnconn.c
    adantr
    #
    wph
    @1
    simpr
    @15
    cC
    cB
    cE
    cP
    cG
    cI
    @3
    tgbtwnconn.p
    @4
    tgbtwnconn.i
    @16
    @19
    @17
    @18
    wph
    @14
    @1
    tgbtwnconn22.5
    adantr
    tgbtwncom
    tgbtwnintr
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
    tgbtwnconn22.1
    tgbtwnconn22.3
    tgbtwnconn22.4
    tgbtwnconn2
    mpjaodan
end
