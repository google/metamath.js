include "co.mm"
include "cmpt2.mm"
include "oveqd.mm"
include "cv.mm"
include "wcel.mm"
include "w3a.mm"
include "wceq.mm"
include "wi.mm"
include "wsbc.mm"
include "eqid.mm"
include "ovmpt4g.mm"
include "a1i.mm"
include "alrimi.mm"
include "spsbcd.mm"
include "wa.mm"
include "adantr.mm"
include "wb.mm"
include "ad2antrr.mm"
include "simpr.mm"
include "adantlr.mm"
include "3eltr4d.mm"
include "eleq1.mm"
include "adantl.mm"
include "mpbird.mm"
include "anassrs.mm"
include "eqeltrd.mm"
include "biimt.mm"
include "syl3anc.mm"
include "oveq12d.mm"
include "eqeq12d.mm"
include "bitr3d.mm"
include "nfeq2.mm"
include "nfan.mm"
include "wnf.mm"
include "nfmpt22.mm"
include "nfcv.mm"
include "nfov.mm"
include "nfeq.mm"
include "sbciedf.mm"
include "nfmpt21.mm"
include "mpbid.mm"
include "eqtrd.mm"

theorem ovmpt2rdxf
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cR: class R
  let cS: class S
  let cF: class F
  let cL: class L
  let cX: class X
  let vk: setvar k
  assume ovmpt2rdx.1: |- ( ph -> F = ( x e. C , y e. D |-> R ) )
  assume ovmpt2rdx.2: |- ( ( ph /\ ( x = A /\ y = B ) ) -> R = S )
  assume ovmpt2rdx.3: |- ( ( ph /\ y = B ) -> C = L )
  assume ovmpt2rdx.4: |- ( ph -> A e. L )
  assume ovmpt2rdx.5: |- ( ph -> B e. D )
  assume ovmpt2rdx.6: |- ( ph -> S e. X )
  assume ovmpt2rdxf.px: |- F/ x ph
  assume ovmpt2rdxf.py: |- F/ y ph
  assume ovmpt2rdxf.ay: |- F/_ y A
  assume ovmpt2rdxf.bx: |- F/_ x B
  assume ovmpt2rdxf.sx: |- F/_ x S
  assume ovmpt2rdxf.sy: |- F/_ y S

  disjoint x y
  disjoint A x
  disjoint B y
  disjoint k x
  assert |- ( ph -> ( A F B ) = S )

  proof
    wph
    cA
    cB
    cF
    co
    cA
    cB
    vx
    vy
    cC
    cD
    cR
    cmpt2
    #
    co
    #
    cS
    wph
    cF
    @0
    cA
    cB
    ovmpt2rdx.1
    oveqd
    wph
    vx
    cv
    #
    cC
    wcel
    #
    vy
    cv
    #
    cD
    wcel
    #
    cR
    cX
    wcel
    #
    w3a
    #
    @2
    @4
    @0
    co
    #
    cR
    wceq
    #
    wi
    #
    vy
    cB
    wsbc
    #
    vx
    cA
    wsbc
    @1
    cS
    wceq
    #
    wph
    @11
    vx
    cA
    cL
    ovmpt2rdx.4
    wph
    @11
    vx
    ovmpt2rdxf.px
    wph
    @10
    vy
    cB
    cD
    ovmpt2rdx.5
    wph
    @10
    vy
    ovmpt2rdxf.py
    @10
    wph
    vx
    vy
    cC
    cD
    cR
    @0
    cX
    @0
    eqid
    ovmpt4g
    a1i
    alrimi
    spsbcd
    alrimi
    spsbcd
    wph
    @11
    @12
    vx
    cA
    cL
    ovmpt2rdx.4
    wph
    @2
    cA
    wceq
    #
    wa
    #
    @10
    @12
    vy
    cB
    cD
    wph
    cB
    cD
    wcel
    #
    @13
    ovmpt2rdx.5
    adantr
    @14
    @4
    cB
    wceq
    #
    wa
    #
    @9
    @10
    @12
    @17
    @3
    @5
    @6
    @9
    @10
    wb
    @17
    cA
    cL
    @2
    cC
    wph
    cA
    cL
    wcel
    @13
    @16
    ovmpt2rdx.4
    ad2antrr
    @14
    @13
    @16
    wph
    @13
    simpr
    adantr
    #
    wph
    @16
    cC
    cL
    wceq
    @13
    ovmpt2rdx.3
    adantlr
    3eltr4d
    @17
    @5
    @15
    wph
    @15
    @13
    @16
    ovmpt2rdx.5
    ad2antrr
    @16
    @5
    @15
    wb
    @14
    @4
    cB
    cD
    eleq1
    adantl
    mpbird
    @17
    cR
    cS
    cX
    wph
    @13
    @16
    cR
    cS
    wceq
    ovmpt2rdx.2
    anassrs
    #
    wph
    cS
    cX
    wcel
    @13
    @16
    ovmpt2rdx.6
    ad2antrr
    eqeltrd
    @7
    @9
    biimt
    syl3anc
    @17
    @8
    @1
    cR
    cS
    @17
    @2
    cA
    @4
    cB
    @0
    @18
    @14
    @16
    simpr
    oveq12d
    @19
    eqeq12d
    bitr3d
    wph
    @13
    vy
    ovmpt2rdxf.py
    vy
    @2
    cA
    ovmpt2rdxf.ay
    nfeq2
    nfan
    @12
    vy
    wnf
    @14
    vy
    @1
    cS
    vy
    cA
    cB
    @0
    ovmpt2rdxf.ay
    vx
    vy
    cC
    cD
    cR
    nfmpt22
    vy
    cB
    nfcv
    nfov
    ovmpt2rdxf.sy
    nfeq
    a1i
    sbciedf
    ovmpt2rdxf.px
    @12
    vx
    wnf
    wph
    vx
    @1
    cS
    vx
    cA
    cB
    @0
    vx
    cA
    nfcv
    vx
    vy
    cC
    cD
    cR
    nfmpt21
    ovmpt2rdxf.bx
    nfov
    ovmpt2rdxf.sx
    nfeq
    a1i
    sbciedf
    mpbid
    eqtrd
end
