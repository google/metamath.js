include "c0.mm"
include "wceq.mm"
include "ciun.mm"
include "wcel.mm"
include "wa.mm"
include "iuneq1.mm"
include "0iun.mm"
include "a1i.mm"
include "eqtrd.mm"
include "adantl.mm"
include "caragen0.mm"
include "adantr.mm"
include "eqeltrd.mm"
include "wn.mm"
include "wne.mm"
include "simpl.mm"
include "neqne.mm"
include "nfv.mm"
include "nfan.mm"
include "cv.mm"
include "adantlr.mm"
include "cun.mm"
include "w3a.mm"
include "come.mm"
include "3ad2ant1.mm"
include "simp2.mm"
include "simp3.mm"
include "caragenuncl.mm"
include "3adant1r.mm"
include "cfn.mm"
include "simpr.mm"
include "fiiuncl.mm"
include "syl2anc.mm"
include "pm2.61dan.mm"

theorem caragenfiiuncl
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cS: class S
  let vk: setvar k
  let cO: class O
  let vx: setvar x
  let vy: setvar y
  assume caragenfiiuncl.kph: |- F/ k ph
  assume caragenfiiuncl.o: |- ( ph -> O e. OutMeas )
  assume caragenfiiuncl.s: |- S = ( CaraGen ` O )
  assume caragenfiiuncl.a: |- ( ph -> A e. Fin )
  assume caragenfiiuncl.b: |- ( ( ph /\ k e. A ) -> B e. S )

  disjoint A k
  disjoint S k
  disjoint A x
  disjoint A y
  disjoint k x
  disjoint k y
  disjoint x y
  disjoint B x
  disjoint B y
  disjoint S x
  disjoint S y
  disjoint ph x
  disjoint ph y
  disjoint k x
  assert |- ( ph -> U_ k e. A B e. S )

  proof
    wph
    cA
    c0
    wceq
    #
    vk
    cA
    cB
    ciun
    #
    cS
    wcel
    #
    wph
    @0
    wa
    @1
    c0
    cS
    @0
    @1
    c0
    wceq
    wph
    @0
    @1
    vk
    c0
    cB
    ciun
    #
    c0
    vk
    cA
    c0
    cB
    iuneq1
    @3
    c0
    wceq
    @0
    vk
    cB
    0iun
    a1i
    eqtrd
    adantl
    wph
    c0
    cS
    wcel
    @0
    wph
    cS
    cO
    caragenfiiuncl.o
    caragenfiiuncl.s
    caragen0
    adantr
    eqeltrd
    wph
    @0
    wn
    #
    wa
    wph
    cA
    c0
    wne
    #
    @2
    wph
    @4
    simpl
    @4
    @5
    wph
    cA
    c0
    neqne
    adantl
    wph
    @5
    wa
    vk
    vx
    vy
    cA
    cB
    cS
    wph
    @5
    vk
    caragenfiiuncl.kph
    @5
    vk
    nfv
    nfan
    wph
    vk
    cv
    cA
    wcel
    cB
    cS
    wcel
    @5
    caragenfiiuncl.b
    adantlr
    wph
    vx
    cv
    #
    cS
    wcel
    #
    vy
    cv
    #
    cS
    wcel
    #
    @6
    @8
    cun
    cS
    wcel
    @5
    wph
    @7
    @9
    w3a
    cS
    @6
    @8
    cO
    wph
    @7
    cO
    come
    wcel
    @9
    caragenfiiuncl.o
    3ad2ant1
    caragenfiiuncl.s
    wph
    @7
    @9
    simp2
    wph
    @7
    @9
    simp3
    caragenuncl
    3adant1r
    wph
    cA
    cfn
    wcel
    @5
    caragenfiiuncl.a
    adantr
    wph
    @5
    simpr
    fiiuncl
    syl2anc
    pm2.61dan
end
