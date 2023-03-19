include "chash.mm"
include "cfv.mm"
include "c1.mm"
include "wceq.mm"
include "co.mm"
include "wcel.mm"
include "wo.mm"
include "c2.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "cds.mm"
include "eqid.mm"
include "cstrkg.mm"
include "adantr.mm"
include "simpr.mm"
include "tgldim0itv.mm"
include "orcd.mm"
include "cv.mm"
include "wne.mm"
include "ad3antrrr.mm"
include "simplr.mm"
include "simprr.mm"
include "necomd.mm"
include "simprl.mm"
include "tgbtwncom.mm"
include "tgbtwnintr.mm"
include "tgbtwnexch3.mm"
include "tgbtwnconn2.mm"
include "tgbtwndiff.mm"
include "r19.29a.mm"
include "cbs.mm"
include "tgldimor.mm"
include "mpjaodan.mm"

theorem tgbtwnconn3
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cP: class P
  let cG: class G
  let cI: class I
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


  assert |- ( ph -> ( B e. ( A I C ) \/ C e. ( A I B ) ) )

  proof
    wph
    cP
    chash
    cfv
    #
    c1
    wceq
    #
    cB
    cA
    cC
    cI
    co
    wcel
    #
    cC
    cA
    cB
    cI
    co
    wcel
    #
    wo
    #
    c2
    @0
    cle
    wbr
    #
    wph
    @1
    wa
    #
    @2
    @3
    @6
    cB
    cA
    cC
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
    cB
    cP
    wcel
    #
    @1
    tgbtwnconn.b
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
    cC
    cP
    wcel
    #
    @1
    tgbtwnconn.c
    adantr
    wph
    @1
    simpr
    tgldim0itv
    orcd
    wph
    @5
    wa
    #
    cA
    cD
    vp
    cv
    #
    cI
    co
    wcel
    #
    cA
    @14
    wne
    #
    wa
    #
    @4
    vp
    cP
    @13
    @14
    cP
    wcel
    #
    wa
    #
    @17
    wa
    #
    @14
    cA
    cB
    cC
    cP
    cG
    cI
    tgbtwnconn.p
    tgbtwnconn.i
    wph
    @9
    @5
    @18
    @17
    tgbtwnconn.g
    ad3antrrr
    #
    @13
    @18
    @17
    simplr
    #
    wph
    @11
    @5
    @18
    @17
    tgbtwnconn.a
    ad3antrrr
    #
    wph
    @10
    @5
    @18
    @17
    tgbtwnconn.b
    ad3antrrr
    #
    wph
    @12
    @5
    @18
    @17
    tgbtwnconn.c
    ad3antrrr
    #
    @20
    cA
    @14
    @19
    @15
    @16
    simprr
    necomd
    @20
    cB
    cA
    @14
    cP
    cG
    cI
    @7
    tgbtwnconn.p
    @8
    tgbtwnconn.i
    @21
    @24
    @23
    @22
    @20
    cB
    cA
    @14
    cD
    cP
    cG
    cI
    @7
    tgbtwnconn.p
    @8
    tgbtwnconn.i
    @21
    @24
    @23
    @22
    wph
    cD
    cP
    wcel
    #
    @5
    @18
    @17
    tgbtwnconn.d
    ad3antrrr
    #
    wph
    cB
    cA
    cD
    cI
    co
    #
    wcel
    @5
    @18
    @17
    tgbtwnconn3.1
    ad3antrrr
    @20
    cD
    cA
    @14
    cP
    cG
    cI
    @7
    tgbtwnconn.p
    @8
    tgbtwnconn.i
    @21
    @27
    @23
    @22
    @19
    @15
    @16
    simprl
    #
    tgbtwncom
    tgbtwnintr
    tgbtwncom
    @20
    cC
    cA
    @14
    cP
    cG
    cI
    @7
    tgbtwnconn.p
    @8
    tgbtwnconn.i
    @21
    @25
    @23
    @22
    @20
    cD
    cC
    cA
    @14
    cP
    cG
    cI
    @7
    tgbtwnconn.p
    @8
    tgbtwnconn.i
    @21
    @27
    @25
    @23
    @22
    @20
    cA
    cC
    cD
    cP
    cG
    cI
    @7
    tgbtwnconn.p
    @8
    tgbtwnconn.i
    @21
    @23
    @25
    @27
    wph
    cC
    @28
    wcel
    @5
    @18
    @17
    tgbtwnconn3.2
    ad3antrrr
    tgbtwncom
    @29
    tgbtwnexch3
    tgbtwncom
    tgbtwnconn2
    @13
    cD
    cA
    cP
    cG
    cI
    @7
    vp
    tgbtwnconn.p
    @8
    tgbtwnconn.i
    wph
    @9
    @5
    tgbtwnconn.g
    adantr
    wph
    @26
    @5
    tgbtwnconn.d
    adantr
    wph
    @11
    @5
    tgbtwnconn.a
    adantr
    wph
    @5
    simpr
    tgbtwndiff
    r19.29a
    wph
    cA
    cP
    cbs
    cG
    tgbtwnconn.p
    tgbtwnconn.a
    tgldimor
    mpjaodan
end
