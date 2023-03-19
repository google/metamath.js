include "co.mm"
include "wcel.mm"
include "wceq.mm"
include "wo.mm"
include "wa.mm"
include "cstrkg.mm"
include "adantr.mm"
include "simpr.mm"
include "btwncolg1.mm"
include "btwncolg3.mm"
include "tgbtwnconn3.mm"
include "mpjaodan.mm"

theorem tgbtwnconnln3
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cP: class P
  let cG: class G
  let cI: class I
  let cL: class L
  let vp: setvar p
  assume tgbtwnconn.p: |- P = ( Base ` G )
  assume tgbtwnconn.i: |- I = ( Itv ` G )
  assume tgbtwnconn.g: |- ( ph -> G e. TarskiG )
  assume tgbtwnconn.a: |- ( ph -> A e. P )
  assume tgbtwnconn.b: |- ( ph -> B e. P )
  assume tgbtwnconn.c: |- ( ph -> C e. P )
  assume tgbtwnconn.d: |- ( ph -> D e. P )
  assume tgbtwnconn3.1: |- ( ph -> B e. ( A I D ) )
  assume tgbtwnconn3.2: |- ( ph -> C e. ( A I D ) )
  assume tgbtwnconnln3.l: |- L = ( LineG ` G )


  assert |- ( ph -> ( B e. ( A L C ) \/ A = C ) )

  proof
    wph
    cB
    cA
    cC
    cI
    co
    wcel
    #
    cB
    cA
    cC
    cL
    co
    wcel
    cA
    cC
    wceq
    wo
    cC
    cA
    cB
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
    cA
    cC
    cB
    tgbtwnconn.p
    tgbtwnconnln3.l
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
    cA
    cP
    wcel
    #
    @0
    tgbtwnconn.a
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
    btwncolg1
    wph
    @1
    wa
    cP
    cG
    cI
    cL
    cA
    cC
    cB
    tgbtwnconn.p
    tgbtwnconnln3.l
    tgbtwnconn.i
    wph
    @2
    @1
    tgbtwnconn.g
    adantr
    wph
    @3
    @1
    tgbtwnconn.a
    adantr
    wph
    @4
    @1
    tgbtwnconn.c
    adantr
    wph
    @5
    @1
    tgbtwnconn.b
    adantr
    wph
    @1
    simpr
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
    tgbtwnconn3.1
    tgbtwnconn3.2
    tgbtwnconn3
    mpjaodan
end
