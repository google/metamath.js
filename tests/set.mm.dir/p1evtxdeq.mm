include "cvtxdg.mm"
include "cfv.mm"
include "cop.mm"
include "csn.mm"
include "cxad.mm"
include "co.mm"
include "cc0.mm"
include "p1evtxdeqlem.mm"
include "cvv.mm"
include "wcel.mm"
include "wa.mm"
include "ciedg.mm"
include "wceq.mm"
include "cvtx.mm"
include "fvex.mm"
include "eqeltri.mm"
include "snex.mm"
include "pm3.2i.mm"
include "opiedgfv.mm"
include "mp1i.mm"
include "opvtxfv.mm"
include "1hevtxdg0.mm"
include "oveq2d.mm"
include "cxnn0.mm"
include "cxr.mm"
include "vtxdgelxnn0.mm"
include "xnn0xr.mm"
include "3syl.mm"
include "xaddid1d.mm"
include "3eqtrd.mm"

theorem p1evtxdeq
  let wph: wff ph
  let cU: class U
  let cE: class E
  let cF: class F
  let cG: class G
  let cI: class I
  let cK: class K
  let cV: class V
  let cX: class X
  let cY: class Y
  assume p1evtxdeq.v: |- V = ( Vtx ` G )
  assume p1evtxdeq.i: |- I = ( iEdg ` G )
  assume p1evtxdeq.f: |- ( ph -> Fun I )
  assume p1evtxdeq.fv: |- ( ph -> ( Vtx ` F ) = V )
  assume p1evtxdeq.fi: |- ( ph -> ( iEdg ` F ) = ( I u. { <. K , E >. } ) )
  assume p1evtxdeq.k: |- ( ph -> K e. X )
  assume p1evtxdeq.d: |- ( ph -> K e/ dom I )
  assume p1evtxdeq.u: |- ( ph -> U e. V )
  assume p1evtxdeq.e: |- ( ph -> E e. Y )
  assume p1evtxdeq.n: |- ( ph -> U e/ E )


  assert |- ( ph -> ( ( VtxDeg ` F ) ` U ) = ( ( VtxDeg ` G ) ` U ) )

  proof
    wph
    cU
    cF
    cvtxdg
    cfv
    cfv
    cU
    cG
    cvtxdg
    cfv
    cfv
    #
    cU
    cV
    cK
    cE
    cop
    #
    csn
    #
    cop
    #
    cvtxdg
    cfv
    cfv
    #
    cxad
    co
    @0
    cc0
    cxad
    co
    @0
    wph
    cU
    cE
    cF
    cG
    cI
    cK
    cV
    cX
    cY
    p1evtxdeq.v
    p1evtxdeq.i
    p1evtxdeq.f
    p1evtxdeq.fv
    p1evtxdeq.fi
    p1evtxdeq.k
    p1evtxdeq.d
    p1evtxdeq.u
    p1evtxdeq.e
    p1evtxdeqlem
    wph
    @4
    cc0
    @0
    cxad
    wph
    cK
    cU
    cE
    @3
    cV
    cX
    cY
    cV
    cvv
    wcel
    #
    @2
    cvv
    wcel
    #
    wa
    #
    @3
    ciedg
    cfv
    @2
    wceq
    wph
    @5
    @6
    cV
    cG
    cvtx
    cfv
    cvv
    p1evtxdeq.v
    cG
    cvtx
    fvex
    eqeltri
    @1
    snex
    pm3.2i
    #
    @2
    cV
    cvv
    cvv
    opiedgfv
    mp1i
    @7
    @3
    cvtx
    cfv
    cV
    wceq
    wph
    @8
    @2
    cV
    cvv
    cvv
    opvtxfv
    mp1i
    p1evtxdeq.k
    p1evtxdeq.u
    p1evtxdeq.e
    p1evtxdeq.n
    1hevtxdg0
    oveq2d
    wph
    @0
    wph
    cU
    cV
    wcel
    @0
    cxnn0
    wcel
    @0
    cxr
    wcel
    p1evtxdeq.u
    cG
    cV
    cU
    p1evtxdeq.v
    vtxdgelxnn0
    @0
    xnn0xr
    3syl
    xaddid1d
    3eqtrd
end
