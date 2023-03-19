include "wcel.mm"
include "wsbc.mm"
include "wa.mm"
include "w3a.mm"
include "csb.mm"
include "wceq.mm"
include "3simpc.mm"
include "simp1.mm"
include "cv.mm"
include "wi.mm"
include "wral.mm"
include "crio.mm"
include "nfra1.mm"
include "nfcv.mm"
include "nfriota.mm"
include "nfcxfr.mm"
include "nfel1.mm"
include "nfv.mm"
include "nfsbc1v.mm"
include "nfan.mm"
include "wnfc.mm"
include "nfcsb1v.mm"
include "a1i.mm"
include "wnf.mm"
include "wb.mm"
include "sbceq1a.mm"
include "adantl.mm"
include "csbeq1a.mm"
include "simpl.mm"
include "simprl.mm"
include "simprr.mm"
include "riotasv2d.mm"
include "syl2anc.mm"

theorem riotasv2s
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cE: class E
  let cV: class V
  assume riotasv2s.2: |- D = ( iota_ x e. A A. y e. B ( ph -> x = C ) )

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B x
  disjoint B y
  disjoint C x
  disjoint E x
  disjoint E y
  disjoint ph x
  assert |- ( ( A e. V /\ D e. A /\ ( E e. B /\ [. E / y ]. ph ) ) -> D = [_ E / y ]_ C )

  proof
    cA
    cV
    wcel
    #
    cD
    cA
    wcel
    #
    cE
    cB
    wcel
    #
    wph
    vy
    cE
    wsbc
    #
    wa
    #
    w3a
    @1
    @4
    wa
    #
    @0
    cD
    vy
    cE
    cC
    csb
    #
    wceq
    @0
    @1
    @4
    3simpc
    @0
    @1
    @4
    simp1
    @5
    wph
    @3
    vx
    vy
    cA
    cB
    cC
    cD
    cE
    @6
    cV
    @1
    @4
    vy
    vy
    cD
    cA
    vy
    cD
    wph
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
    riotasv2s.2
    @8
    vy
    vx
    cA
    @7
    vy
    cB
    nfra1
    vy
    cA
    nfcv
    nfriota
    nfcxfr
    nfel1
    @2
    @3
    vy
    @2
    vy
    nfv
    wph
    vy
    cE
    nfsbc1v
    #
    nfan
    nfan
    vy
    @6
    wnfc
    @5
    vy
    cE
    cC
    nfcsb1v
    a1i
    @3
    vy
    wnf
    @5
    @10
    a1i
    cD
    @9
    wceq
    @5
    riotasv2s.2
    a1i
    vy
    cv
    cE
    wceq
    #
    wph
    @3
    wb
    @5
    wph
    vy
    cE
    sbceq1a
    adantl
    @11
    cC
    @6
    wceq
    @5
    vy
    cE
    cC
    csbeq1a
    adantl
    @1
    @4
    simpl
    @1
    @2
    @3
    simprl
    @1
    @2
    @3
    simprr
    riotasv2d
    syl2anc
end
