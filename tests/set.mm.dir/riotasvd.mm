include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "wceq.mm"
include "wi.mm"
include "wral.mm"
include "crio.mm"
include "wsbc.mm"
include "wreu.mm"
include "adantr.mm"
include "eqeltrrd.mm"
include "wb.mm"
include "riotaclbgBAD.mm"
include "adantl.mm"
include "mpbird.mm"
include "riotasbc.mm"
include "syl.mm"
include "eqeq1.mm"
include "imbi2d.mm"
include "ralbidv.mm"
include "nfra1.mm"
include "nfcv.mm"
include "nfriota.mm"
include "nfeq2.mm"
include "ralbid.mm"
include "sbcie2g.mm"
include "mpbid.mm"
include "rsp.mm"
include "impd.mm"
include "eqeq1d.mm"
include "sylibrd.mm"

theorem riotasvd
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cV: class V
  let vz: setvar z
  assume riotasvd.1: |- ( ph -> D = ( iota_ x e. A A. y e. B ( ps -> x = C ) ) )
  assume riotasvd.2: |- ( ph -> D e. A )

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B x
  disjoint C x
  disjoint ps x
  disjoint x z
  disjoint y z
  disjoint A z
  disjoint B z
  disjoint C z
  disjoint D z
  disjoint ph z
  disjoint ps z
  assert |- ( ( ph /\ A e. V ) -> ( ( y e. B /\ ps ) -> D = C ) )

  proof
    wph
    cA
    cV
    wcel
    #
    wa
    #
    vy
    cv
    cB
    wcel
    #
    wps
    wa
    wps
    vx
    cv
    #
    cC
    wceq
    #
    wi
    #
    vy
    cB
    wral
    #
    vx
    cA
    crio
    #
    cC
    wceq
    #
    cD
    cC
    wceq
    @1
    @2
    wps
    @8
    @1
    wps
    @8
    wi
    #
    vy
    cB
    wral
    #
    @2
    @9
    wi
    @1
    @6
    vx
    @7
    wsbc
    #
    @10
    @1
    @6
    vx
    cA
    wreu
    #
    @11
    @1
    @12
    @7
    cA
    wcel
    #
    @1
    cD
    @7
    cA
    wph
    cD
    @7
    wceq
    @0
    riotasvd.1
    adantr
    #
    wph
    cD
    cA
    wcel
    @0
    riotasvd.2
    adantr
    eqeltrrd
    #
    @0
    @12
    @13
    wb
    wph
    @6
    vx
    cA
    cV
    riotaclbgBAD
    adantl
    mpbird
    @6
    vx
    cA
    riotasbc
    syl
    @1
    @13
    @11
    @10
    wb
    @15
    @6
    wps
    vz
    cv
    #
    cC
    wceq
    #
    wi
    #
    vy
    cB
    wral
    @10
    vx
    vz
    @7
    cA
    @3
    @16
    wceq
    #
    @5
    @18
    vy
    cB
    @19
    @4
    @17
    wps
    @3
    @16
    cC
    eqeq1
    imbi2d
    ralbidv
    @16
    @7
    wceq
    #
    @18
    @9
    vy
    cB
    vy
    @16
    @7
    @6
    vy
    vx
    cA
    @5
    vy
    cB
    nfra1
    vy
    cA
    nfcv
    nfriota
    nfeq2
    @20
    @17
    @8
    wps
    @16
    @7
    cC
    eqeq1
    imbi2d
    ralbid
    sbcie2g
    syl
    mpbid
    @9
    vy
    cB
    rsp
    syl
    impd
    @1
    cD
    @7
    cC
    @14
    eqeq1d
    sylibrd
end
