include "cvtxdg.mm"
include "cfv.mm"
include "cop.mm"
include "csn.mm"
include "cxad.mm"
include "co.mm"
include "c1.mm"
include "cpw.mm"
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
include "1hevtxdg1.mm"
include "oveq2d.mm"
include "eqtrd.mm"

theorem p1evtxdp1
  let wph: wff ph
  let cU: class U
  let cE: class E
  let cF: class F
  let cG: class G
  let cI: class I
  let cK: class K
  let cV: class V
  let cX: class X
  assume p1evtxdeq.v: |- V = ( Vtx ` G )
  assume p1evtxdeq.i: |- I = ( iEdg ` G )
  assume p1evtxdeq.f: |- ( ph -> Fun I )
  assume p1evtxdeq.fv: |- ( ph -> ( Vtx ` F ) = V )
  assume p1evtxdeq.fi: |- ( ph -> ( iEdg ` F ) = ( I u. { <. K , E >. } ) )
  assume p1evtxdeq.k: |- ( ph -> K e. X )
  assume p1evtxdeq.d: |- ( ph -> K e/ dom I )
  assume p1evtxdeq.u: |- ( ph -> U e. V )
  assume p1evtxdp1.e: |- ( ph -> E e. ~P V )
  assume p1evtxdp1.n: |- ( ph -> U e. E )
  assume p1evtxdp1.l: |- ( ph -> 2 <_ ( # ` E ) )


  assert |- ( ph -> ( ( VtxDeg ` F ) ` U ) = ( ( ( VtxDeg ` G ) ` U ) +e 1 ) )

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
    c1
    cxad
    co
    wph
    cU
    cE
    cF
    cG
    cI
    cK
    cV
    cX
    cV
    cpw
    p1evtxdeq.v
    p1evtxdeq.i
    p1evtxdeq.f
    p1evtxdeq.fv
    p1evtxdeq.fi
    p1evtxdeq.k
    p1evtxdeq.d
    p1evtxdeq.u
    p1evtxdp1.e
    p1evtxdeqlem
    wph
    @4
    c1
    @0
    cxad
    wph
    cK
    cU
    cE
    @3
    cV
    cX
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
    p1evtxdp1.e
    p1evtxdp1.n
    p1evtxdp1.l
    1hevtxdg1
    oveq2d
    eqtrd
end
