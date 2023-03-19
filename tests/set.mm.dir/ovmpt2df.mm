include "cv.mm"
include "wceq.mm"
include "cmpt2.mm"
include "wi.mm"
include "nfv.mm"
include "nfmpt21.mm"
include "nfeq.mm"
include "nfim.mm"
include "cvv.mm"
include "wcel.mm"
include "wex.mm"
include "elex.mm"
include "syl.mm"
include "isset.mm"
include "sylib.mm"
include "wa.mm"
include "nfmpt22.mm"
include "co.mm"
include "oveq.mm"
include "simprl.mm"
include "simprr.mm"
include "oveq12d.mm"
include "adantr.mm"
include "eqeltrd.mm"
include "adantrr.mm"
include "eqid.mm"
include "ovmpt4g.mm"
include "syl3anc.mm"
include "eqtr3d.mm"
include "eqeq2d.mm"
include "sylbid.mm"
include "syl5.mm"
include "expr.mm"
include "exlimd.mm"
include "mpd.mm"
include "exlimdd.mm"

theorem ovmpt2df
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cR: class R
  let cF: class F
  let cV: class V
  assume ovmpt2df.1: |- ( ph -> A e. C )
  assume ovmpt2df.2: |- ( ( ph /\ x = A ) -> B e. D )
  assume ovmpt2df.3: |- ( ( ph /\ ( x = A /\ y = B ) ) -> R e. V )
  assume ovmpt2df.4: |- ( ( ph /\ ( x = A /\ y = B ) ) -> ( ( A F B ) = R -> ps ) )
  assume ovmpt2df.5: |- F/_ x F
  assume ovmpt2df.6: |- F/ x ps
  assume ovmpt2df.7: |- F/_ y F
  assume ovmpt2df.8: |- F/ y ps

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B y
  disjoint ph x
  disjoint ph y
  assert |- ( ph -> ( F = ( x e. C , y e. D |-> R ) -> ps ) )

  proof
    wph
    vx
    cv
    #
    cA
    wceq
    #
    cF
    vx
    vy
    cC
    cD
    cR
    cmpt2
    #
    wceq
    #
    wps
    wi
    #
    vx
    wph
    vx
    nfv
    @3
    wps
    vx
    vx
    cF
    @2
    ovmpt2df.5
    vx
    vy
    cC
    cD
    cR
    nfmpt21
    nfeq
    ovmpt2df.6
    nfim
    wph
    cA
    cvv
    wcel
    #
    @1
    vx
    wex
    wph
    cA
    cC
    wcel
    #
    @5
    ovmpt2df.1
    cA
    cC
    elex
    syl
    vx
    cA
    isset
    sylib
    wph
    @1
    wa
    #
    vy
    cv
    #
    cB
    wceq
    #
    vy
    wex
    #
    @4
    @7
    cB
    cvv
    wcel
    #
    @10
    @7
    cB
    cD
    wcel
    #
    @11
    ovmpt2df.2
    cB
    cD
    elex
    syl
    vy
    cB
    isset
    sylib
    @7
    @9
    @4
    vy
    @7
    vy
    nfv
    @3
    wps
    vy
    vy
    cF
    @2
    ovmpt2df.7
    vx
    vy
    cC
    cD
    cR
    nfmpt22
    nfeq
    ovmpt2df.8
    nfim
    wph
    @1
    @9
    @4
    @3
    cA
    cB
    cF
    co
    #
    cA
    cB
    @2
    co
    #
    wceq
    #
    wph
    @1
    @9
    wa
    #
    wa
    #
    wps
    cA
    cB
    cF
    @2
    oveq
    @17
    @15
    @13
    cR
    wceq
    wps
    @17
    @14
    cR
    @13
    @17
    @0
    @8
    @2
    co
    #
    @14
    cR
    @17
    @0
    cA
    @8
    cB
    @2
    wph
    @1
    @9
    simprl
    #
    wph
    @1
    @9
    simprr
    #
    oveq12d
    @17
    @0
    cC
    wcel
    @8
    cD
    wcel
    cR
    cV
    wcel
    @18
    cR
    wceq
    @17
    @0
    cA
    cC
    @19
    wph
    @6
    @16
    ovmpt2df.1
    adantr
    eqeltrd
    @17
    @8
    cB
    cD
    @20
    wph
    @1
    @12
    @9
    ovmpt2df.2
    adantrr
    eqeltrd
    ovmpt2df.3
    vx
    vy
    cC
    cD
    cR
    @2
    cV
    @2
    eqid
    ovmpt4g
    syl3anc
    eqtr3d
    eqeq2d
    ovmpt2df.4
    sylbid
    syl5
    expr
    exlimd
    mpd
    exlimdd
end
