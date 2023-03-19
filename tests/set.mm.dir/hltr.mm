include "cfv.mm"
include "wbr.mm"
include "wne.mm"
include "co.mm"
include "wcel.mm"
include "wo.mm"
include "w3a.mm"
include "cstrkg.mm"
include "hlne1.mm"
include "hlne2.mm"
include "wa.mm"
include "cds.mm"
include "eqid.mm"
include "ad2antrr.mm"
include "simplr.mm"
include "simpr.mm"
include "tgbtwnexch.mm"
include "orcd.mm"
include "tgbtwnconn3.mm"
include "ishlg.mm"
include "mpbid.mm"
include "simp3d.mm"
include "adantr.mm"
include "mpjaodan.mm"
include "simp1d.mm"
include "necomd.mm"
include "tgbtwnconn1.mm"
include "olcd.mm"
include "3jca.mm"
include "mpbird.mm"

theorem hltr
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
  assume hltr.1: |- ( ph -> A ( K ` D ) B )
  assume hltr.2: |- ( ph -> B ( K ` D ) C )


  assert |- ( ph -> A ( K ` D ) C )

  proof
    wph
    cA
    cC
    cD
    cK
    cfv
    #
    wbr
    cA
    cD
    wne
    #
    cC
    cD
    wne
    #
    cA
    cD
    cC
    cI
    co
    #
    wcel
    #
    cC
    cD
    cA
    cI
    co
    #
    wcel
    #
    wo
    #
    w3a
    wph
    @1
    @2
    @7
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
    hltr.1
    hlne1
    wph
    cB
    cC
    cD
    cP
    cG
    cI
    cK
    cstrkg
    ishlg.p
    ishlg.i
    ishlg.k
    ishlg.b
    ishlg.c
    hltr.d
    hlln.1
    hltr.2
    hlne2
    wph
    cA
    cD
    cB
    cI
    co
    #
    wcel
    #
    @7
    cB
    @5
    wcel
    #
    wph
    @9
    wa
    #
    cB
    @3
    wcel
    #
    @7
    cC
    @8
    wcel
    #
    @11
    @12
    wa
    #
    @4
    @6
    @14
    cD
    cA
    cB
    cC
    cP
    cG
    cI
    cG
    cds
    cfv
    #
    ishlg.p
    @15
    eqid
    #
    ishlg.i
    wph
    cG
    cstrkg
    wcel
    #
    @9
    @12
    hlln.1
    ad2antrr
    wph
    cD
    cP
    wcel
    #
    @9
    @12
    hltr.d
    ad2antrr
    wph
    cA
    cP
    wcel
    #
    @9
    @12
    ishlg.a
    ad2antrr
    wph
    cB
    cP
    wcel
    #
    @9
    @12
    ishlg.b
    ad2antrr
    wph
    cC
    cP
    wcel
    #
    @9
    @12
    ishlg.c
    ad2antrr
    wph
    @9
    @12
    simplr
    @11
    @12
    simpr
    tgbtwnexch
    orcd
    @11
    @13
    wa
    cD
    cA
    cC
    cB
    cP
    cG
    cI
    ishlg.p
    ishlg.i
    wph
    @17
    @9
    @13
    hlln.1
    ad2antrr
    wph
    @18
    @9
    @13
    hltr.d
    ad2antrr
    wph
    @19
    @9
    @13
    ishlg.a
    ad2antrr
    wph
    @21
    @9
    @13
    ishlg.c
    ad2antrr
    wph
    @20
    @9
    @13
    ishlg.b
    ad2antrr
    wph
    @9
    @13
    simplr
    @11
    @13
    simpr
    tgbtwnconn3
    wph
    @12
    @13
    wo
    #
    @9
    wph
    cB
    cD
    wne
    #
    @2
    @22
    wph
    cB
    cC
    @0
    wbr
    @23
    @2
    @22
    w3a
    hltr.2
    wph
    cB
    cC
    cD
    cP
    cG
    cI
    cK
    cstrkg
    ishlg.p
    ishlg.i
    ishlg.k
    ishlg.b
    ishlg.c
    hltr.d
    hlln.1
    ishlg
    mpbid
    #
    simp3d
    #
    adantr
    mpjaodan
    wph
    @10
    wa
    #
    @12
    @7
    @13
    @26
    @12
    wa
    cD
    cB
    cA
    cC
    cP
    cG
    cI
    ishlg.p
    ishlg.i
    wph
    @17
    @10
    @12
    hlln.1
    ad2antrr
    wph
    @18
    @10
    @12
    hltr.d
    ad2antrr
    wph
    @20
    @10
    @12
    ishlg.b
    ad2antrr
    wph
    @19
    @10
    @12
    ishlg.a
    ad2antrr
    wph
    @21
    @10
    @12
    ishlg.c
    ad2antrr
    wph
    cD
    cB
    wne
    @10
    @12
    wph
    cB
    cD
    wph
    @23
    @2
    @22
    @24
    simp1d
    necomd
    ad2antrr
    wph
    @10
    @12
    simplr
    @26
    @12
    simpr
    tgbtwnconn1
    @26
    @13
    wa
    #
    @6
    @4
    @27
    cD
    cC
    cB
    cA
    cP
    cG
    cI
    @15
    ishlg.p
    @16
    ishlg.i
    wph
    @17
    @10
    @13
    hlln.1
    ad2antrr
    wph
    @18
    @10
    @13
    hltr.d
    ad2antrr
    wph
    @21
    @10
    @13
    ishlg.c
    ad2antrr
    wph
    @20
    @10
    @13
    ishlg.b
    ad2antrr
    wph
    @19
    @10
    @13
    ishlg.a
    ad2antrr
    @26
    @13
    simpr
    wph
    @10
    @13
    simplr
    tgbtwnexch
    olcd
    wph
    @22
    @10
    @25
    adantr
    mpjaodan
    wph
    @1
    @23
    @9
    @10
    wo
    #
    wph
    cA
    cB
    @0
    wbr
    @1
    @23
    @28
    w3a
    hltr.1
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
    simp3d
    mpjaodan
    3jca
    wph
    cA
    cC
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
    ishlg.c
    hltr.d
    hlln.1
    ishlg
    mpbird
end
