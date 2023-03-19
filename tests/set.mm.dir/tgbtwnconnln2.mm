include "co.mm"
include "wcel.mm"
include "wceq.mm"
include "wo.mm"
include "wa.mm"
include "cstrkg.mm"
include "adantr.mm"
include "simpr.mm"
include "btwncolg2.mm"
include "cds.mm"
include "cfv.mm"
include "eqid.mm"
include "tgbtwncom.mm"
include "btwncolg3.mm"
include "tgbtwnconn2.mm"
include "mpjaodan.mm"

theorem tgbtwnconnln2
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cP: class P
  let cG: class G
  let cI: class I
  let cL: class L
  assume tgbtwnconn.p: |- P = ( Base ` G )
  assume tgbtwnconn.i: |- I = ( Itv ` G )
  assume tgbtwnconn.g: |- ( ph -> G e. TarskiG )
  assume tgbtwnconn.a: |- ( ph -> A e. P )
  assume tgbtwnconn.b: |- ( ph -> B e. P )
  assume tgbtwnconn.c: |- ( ph -> C e. P )
  assume tgbtwnconn.d: |- ( ph -> D e. P )
  assume tgbtwnconnln1.l: |- L = ( LineG ` G )
  assume tgbtwnconnln1.1: |- ( ph -> A =/= B )
  assume tgbtwnconnln1.2: |- ( ph -> B e. ( A I C ) )
  assume tgbtwnconnln1.3: |- ( ph -> B e. ( A I D ) )


  assert |- ( ph -> ( B e. ( C L D ) \/ C = D ) )

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
    cC
    cD
    cL
    co
    wcel
    cC
    cD
    wceq
    wo
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
    cP
    cG
    cI
    cL
    cC
    cD
    cB
    tgbtwnconn.p
    tgbtwnconnln1.l
    tgbtwnconn.i
    wph
    cG
    cstrkg
    wcel
    #
    @0
    tgbtwnconn.g
    adantr
    wph
    cC
    cP
    wcel
    #
    @0
    tgbtwnconn.c
    adantr
    wph
    cD
    cP
    wcel
    #
    @0
    tgbtwnconn.d
    adantr
    wph
    cB
    cP
    wcel
    #
    @0
    tgbtwnconn.b
    adantr
    wph
    @0
    simpr
    btwncolg2
    wph
    @1
    wa
    #
    cP
    cG
    cI
    cL
    cC
    cD
    cB
    tgbtwnconn.p
    tgbtwnconnln1.l
    tgbtwnconn.i
    wph
    @2
    @1
    tgbtwnconn.g
    adantr
    #
    wph
    @3
    @1
    tgbtwnconn.c
    adantr
    #
    wph
    @4
    @1
    tgbtwnconn.d
    adantr
    #
    wph
    @5
    @1
    tgbtwnconn.b
    adantr
    #
    @6
    cB
    cD
    cC
    cP
    cG
    cI
    cG
    cds
    cfv
    #
    tgbtwnconn.p
    @11
    eqid
    tgbtwnconn.i
    @7
    @10
    @9
    @8
    wph
    @1
    simpr
    tgbtwncom
    btwncolg3
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
    tgbtwnconnln1.1
    tgbtwnconnln1.2
    tgbtwnconnln1.3
    tgbtwnconn2
    mpjaodan
end
