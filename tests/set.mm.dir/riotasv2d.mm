include "wcel.mm"
include "cvv.mm"
include "wceq.mm"
include "elex.mm"
include "wa.mm"
include "adantr.mm"
include "cv.mm"
include "wi.mm"
include "wb.mm"
include "eleq1.mm"
include "adantl.mm"
include "anbi12d.mm"
include "eqeq2d.mm"
include "imbi12d.mm"
include "adantlr.mm"
include "riotasvd.mm"
include "nfv.mm"
include "nfan.mm"
include "nfcvd.mm"
include "wnf.mm"
include "nfvd.mm"
include "nfand.mm"
include "wnfc.mm"
include "wral.mm"
include "crio.mm"
include "nfra1.mm"
include "nfcv.mm"
include "nfriota.mm"
include "nfceqdf.mm"
include "mpbiri.mm"
include "nfeqd.mm"
include "nfimd.mm"
include "vtocldf.mm"
include "mp2and.mm"
include "sylan2.mm"

theorem riotasv2d
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cE: class E
  let cF: class F
  let cV: class V
  assume riotasv2d.1: |- F/ y ph
  assume riotasv2d.2: |- ( ph -> F/_ y F )
  assume riotasv2d.3: |- ( ph -> F/ y ch )
  assume riotasv2d.4: |- ( ph -> D = ( iota_ x e. A A. y e. B ( ps -> x = C ) ) )
  assume riotasv2d.5: |- ( ( ph /\ y = E ) -> ( ps <-> ch ) )
  assume riotasv2d.6: |- ( ( ph /\ y = E ) -> C = F )
  assume riotasv2d.7: |- ( ph -> D e. A )
  assume riotasv2d.8: |- ( ph -> E e. B )
  assume riotasv2d.9: |- ( ph -> ch )

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B x
  disjoint B y
  disjoint C x
  disjoint E y
  disjoint ps x
  assert |- ( ( ph /\ A e. V ) -> D = F )

  proof
    cA
    cV
    wcel
    wph
    cA
    cvv
    wcel
    #
    cD
    cF
    wceq
    #
    cA
    cV
    elex
    wph
    @0
    wa
    #
    cE
    cB
    wcel
    #
    wch
    @1
    wph
    @3
    @0
    riotasv2d.8
    adantr
    #
    wph
    wch
    @0
    riotasv2d.9
    adantr
    @2
    vy
    cv
    #
    cB
    wcel
    #
    wps
    wa
    #
    cD
    cC
    wceq
    #
    wi
    #
    @3
    wch
    wa
    #
    @1
    wi
    #
    vy
    cE
    cB
    @4
    wph
    @5
    cE
    wceq
    #
    @9
    @11
    wb
    @0
    wph
    @12
    wa
    #
    @7
    @10
    @8
    @1
    @13
    @6
    @3
    wps
    wch
    @12
    @6
    @3
    wb
    wph
    @5
    cE
    cB
    eleq1
    adantl
    riotasv2d.5
    anbi12d
    @13
    cC
    cF
    cD
    riotasv2d.6
    eqeq2d
    imbi12d
    adantlr
    wph
    wps
    vx
    vy
    cA
    cB
    cC
    cD
    cvv
    riotasv2d.4
    riotasv2d.7
    riotasvd
    wph
    @0
    vy
    riotasv2d.1
    @0
    vy
    nfv
    nfan
    @2
    vy
    cE
    nfcvd
    wph
    @11
    vy
    wnf
    @0
    wph
    @10
    @1
    vy
    wph
    @3
    wch
    vy
    wph
    @3
    vy
    nfvd
    riotasv2d.3
    nfand
    wph
    vy
    cD
    cF
    wph
    vy
    cD
    wnfc
    vy
    wps
    vx
    cv
    cC
    wceq
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
    wnfc
    @15
    vy
    vx
    cA
    @14
    vy
    cB
    nfra1
    vy
    cA
    nfcv
    nfriota
    wph
    vy
    cD
    @16
    riotasv2d.1
    riotasv2d.4
    nfceqdf
    mpbiri
    riotasv2d.2
    nfeqd
    nfimd
    adantr
    vtocldf
    mp2and
    sylan2
end
