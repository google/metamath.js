include "cc0.mm"
include "clt.mm"
include "wbr.mm"
include "wceq.mm"
include "w3o.mm"
include "cxr.mm"
include "wcel.mm"
include "0xr.mm"
include "wor.mm"
include "wa.mm"
include "xrltso.mm"
include "solin.mm"
include "mpan.mm"
include "sylancl.mm"
include "cxne.mm"
include "wb.mm"
include "xlt0neg1.mm"
include "syl.mm"
include "wi.mm"
include "xnegcl.mm"
include "cv.mm"
include "breq2.mm"
include "imbi12d.mm"
include "imbi2d.mm"
include "exp32.mm"
include "com12.mm"
include "vtoclga.mm"
include "mpcom.mm"
include "sylbid.mm"
include "eqeq12d.mm"
include "xneg11.mm"
include "syl2anc.mm"
include "bitrd.mm"
include "sylibd.mm"
include "eqeq1.mm"
include "vtoclg.mm"
include "3jaod.mm"
include "mpd.mm"

theorem xmulasslem
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cD: class D
  let cE: class E
  let cF: class F
  let cX: class X
  let cY: class Y
  assume xmulasslem.1: |- ( x = D -> ( ps <-> X = Y ) )
  assume xmulasslem.2: |- ( x = -e D -> ( ps <-> E = F ) )
  assume xmulasslem.x: |- ( ph -> X e. RR* )
  assume xmulasslem.y: |- ( ph -> Y e. RR* )
  assume xmulasslem.d: |- ( ph -> D e. RR* )
  assume xmulasslem.ps: |- ( ( ph /\ ( x e. RR* /\ 0 < x ) ) -> ps )
  assume xmulasslem.0: |- ( ph -> ( x = 0 -> ps ) )
  assume xmulasslem.e: |- ( ph -> E = -e X )
  assume xmulasslem.f: |- ( ph -> F = -e Y )

  disjoint D x
  disjoint E x
  disjoint F x
  disjoint ph x
  disjoint X x
  disjoint Y x
  assert |- ( ph -> X = Y )

  proof
    wph
    cD
    cc0
    clt
    wbr
    #
    cD
    cc0
    wceq
    #
    cc0
    cD
    clt
    wbr
    #
    w3o
    #
    cX
    cY
    wceq
    #
    wph
    cD
    cxr
    wcel
    #
    cc0
    cxr
    wcel
    #
    @3
    xmulasslem.d
    0xr
    cxr
    clt
    wor
    @5
    @6
    wa
    @3
    xrltso
    cxr
    cD
    cc0
    clt
    solin
    mpan
    sylancl
    wph
    @0
    @4
    @1
    @2
    wph
    @0
    cE
    cF
    wceq
    #
    @4
    wph
    @0
    cc0
    cD
    cxne
    #
    clt
    wbr
    #
    @7
    wph
    @5
    @0
    @9
    wb
    xmulasslem.d
    cD
    xlt0neg1
    syl
    @8
    cxr
    wcel
    #
    wph
    @9
    @7
    wi
    #
    wph
    @5
    @10
    xmulasslem.d
    cD
    xnegcl
    syl
    wph
    cc0
    vx
    cv
    #
    clt
    wbr
    #
    wps
    wi
    #
    wi
    #
    wph
    @11
    wi
    vx
    @8
    cxr
    @12
    @8
    wceq
    #
    @14
    @11
    wph
    @16
    @13
    @9
    wps
    @7
    @12
    @8
    cc0
    clt
    breq2
    xmulasslem.2
    imbi12d
    imbi2d
    wph
    @12
    cxr
    wcel
    #
    @14
    wph
    @17
    @13
    wps
    xmulasslem.ps
    exp32
    com12
    #
    vtoclga
    mpcom
    sylbid
    wph
    @7
    cX
    cxne
    #
    cY
    cxne
    #
    wceq
    #
    @4
    wph
    cE
    @19
    cF
    @20
    xmulasslem.e
    xmulasslem.f
    eqeq12d
    wph
    cX
    cxr
    wcel
    cY
    cxr
    wcel
    @21
    @4
    wb
    xmulasslem.x
    xmulasslem.y
    cX
    cY
    xneg11
    syl2anc
    bitrd
    sylibd
    @5
    wph
    @1
    @4
    wi
    #
    xmulasslem.d
    wph
    @12
    cc0
    wceq
    #
    wps
    wi
    #
    wi
    wph
    @22
    wi
    vx
    cD
    cxr
    @12
    cD
    wceq
    #
    @24
    @22
    wph
    @25
    @23
    @1
    wps
    @4
    @12
    cD
    cc0
    eqeq1
    xmulasslem.1
    imbi12d
    imbi2d
    xmulasslem.0
    vtoclg
    mpcom
    @5
    wph
    @2
    @4
    wi
    #
    xmulasslem.d
    @15
    wph
    @26
    wi
    vx
    cD
    cxr
    @25
    @14
    @26
    wph
    @25
    @13
    @2
    wps
    @4
    @12
    cD
    cc0
    clt
    breq2
    xmulasslem.1
    imbi12d
    imbi2d
    @18
    vtoclga
    mpcom
    3jaod
    mpd
end
