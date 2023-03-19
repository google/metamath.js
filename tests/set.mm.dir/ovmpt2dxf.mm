include "co.mm"
include "cmpt2.mm"
include "oveqd.mm"
include "cv.mm"
include "wcel.mm"
include "cvv.mm"
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
include "simplr.mm"
include "ad2antrr.mm"
include "eqeltrd.mm"
include "simpr.mm"
include "3eltr4d.mm"
include "anassrs.mm"
include "elex.mm"
include "syl.mm"
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

theorem ovmpt2dxf
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
  assume ovmpt2dx.1: |- ( ph -> F = ( x e. C , y e. D |-> R ) )
  assume ovmpt2dx.2: |- ( ( ph /\ ( x = A /\ y = B ) ) -> R = S )
  assume ovmpt2dx.3: |- ( ( ph /\ x = A ) -> D = L )
  assume ovmpt2dx.4: |- ( ph -> A e. C )
  assume ovmpt2dx.5: |- ( ph -> B e. L )
  assume ovmpt2dx.6: |- ( ph -> S e. X )
  assume ovmpt2dxf.px: |- F/ x ph
  assume ovmpt2dxf.py: |- F/ y ph
  assume ovmpt2dxf.ay: |- F/_ y A
  assume ovmpt2dxf.bx: |- F/_ x B
  assume ovmpt2dxf.sx: |- F/_ x S
  assume ovmpt2dxf.sy: |- F/_ y S

  disjoint x y
  disjoint A x
  disjoint B y
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
    ovmpt2dx.1
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
    cvv
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
    cC
    ovmpt2dx.4
    wph
    @11
    vx
    ovmpt2dxf.px
    wph
    @10
    vy
    cB
    cL
    ovmpt2dx.5
    wph
    @10
    vy
    ovmpt2dxf.py
    @10
    wph
    vx
    vy
    cC
    cD
    cR
    @0
    cvv
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
    cC
    ovmpt2dx.4
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
    cL
    wph
    cB
    cL
    wcel
    #
    @13
    ovmpt2dx.5
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
    @2
    cA
    cC
    wph
    @13
    @16
    simplr
    #
    wph
    cA
    cC
    wcel
    @13
    @16
    ovmpt2dx.4
    ad2antrr
    eqeltrd
    @17
    cB
    cL
    @4
    cD
    wph
    @15
    @13
    @16
    ovmpt2dx.5
    ad2antrr
    @14
    @16
    simpr
    #
    @14
    cD
    cL
    wceq
    @16
    ovmpt2dx.3
    adantr
    3eltr4d
    @17
    cR
    cS
    cvv
    wph
    @13
    @16
    cR
    cS
    wceq
    ovmpt2dx.2
    anassrs
    #
    wph
    cS
    cvv
    wcel
    #
    @13
    @16
    wph
    cS
    cX
    wcel
    @21
    ovmpt2dx.6
    cS
    cX
    elex
    syl
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
    @19
    oveq12d
    @20
    eqeq12d
    bitr3d
    wph
    @13
    vy
    ovmpt2dxf.py
    vy
    @2
    cA
    ovmpt2dxf.ay
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
    ovmpt2dxf.ay
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
    ovmpt2dxf.sy
    nfeq
    a1i
    sbciedf
    ovmpt2dxf.px
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
    ovmpt2dxf.bx
    nfov
    ovmpt2dxf.sx
    nfeq
    a1i
    sbciedf
    mpbid
    eqtrd
end
