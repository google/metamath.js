include "cop.mm"
include "csn.mm"
include "cvv.mm"
include "wcel.mm"
include "wa.mm"
include "ciedg.mm"
include "cfv.mm"
include "wceq.mm"
include "cvtx.mm"
include "fvex.mm"
include "eqeltri.mm"
include "snex.mm"
include "pm3.2i.mm"
include "opiedgfv.mm"
include "eqcomd.mm"
include "ax-mp.mm"
include "opvtxfv.mm"
include "mp1i.mm"
include "cdm.mm"
include "cin.mm"
include "c0.mm"
include "dmsnopg.mm"
include "syl.mm"
include "ineq2d.mm"
include "wn.mm"
include "wnel.mm"
include "df-nel.mm"
include "sylib.mm"
include "disjsn.mm"
include "sylibr.mm"
include "eqtrd.mm"
include "wfun.mm"
include "funsng.mm"
include "syl2anc.mm"
include "vtxdun.mm"

theorem p1evtxdeqlem
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


  assert |- ( ph -> ( ( VtxDeg ` F ) ` U ) = ( ( ( VtxDeg ` G ) ` U ) +e ( ( VtxDeg ` <. V , { <. K , E >. } >. ) ` U ) ) )

  proof
    wph
    cF
    cG
    cV
    cK
    cE
    cop
    #
    csn
    #
    cop
    #
    cI
    @1
    cU
    cV
    p1evtxdeq.i
    cV
    cvv
    wcel
    #
    @1
    cvv
    wcel
    #
    wa
    #
    @1
    @2
    ciedg
    cfv
    #
    wceq
    @3
    @4
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
    @0
    snex
    pm3.2i
    #
    @5
    @6
    @1
    @1
    cV
    cvv
    cvv
    opiedgfv
    eqcomd
    ax-mp
    p1evtxdeq.v
    @5
    @2
    cvtx
    cfv
    cV
    wceq
    wph
    @7
    @1
    cV
    cvv
    cvv
    opvtxfv
    mp1i
    p1evtxdeq.fv
    wph
    cI
    cdm
    #
    @1
    cdm
    #
    cin
    @8
    cK
    csn
    #
    cin
    #
    c0
    wph
    @9
    @10
    @8
    wph
    cE
    cY
    wcel
    #
    @9
    @10
    wceq
    p1evtxdeq.e
    cK
    cE
    cY
    dmsnopg
    syl
    ineq2d
    wph
    cK
    @8
    wcel
    wn
    #
    @11
    c0
    wceq
    wph
    cK
    @8
    wnel
    @13
    p1evtxdeq.d
    cK
    @8
    df-nel
    sylib
    @8
    cK
    disjsn
    sylibr
    eqtrd
    p1evtxdeq.f
    wph
    cK
    cX
    wcel
    @12
    @1
    wfun
    p1evtxdeq.k
    p1evtxdeq.e
    cK
    cE
    cX
    cY
    funsng
    syl2anc
    p1evtxdeq.u
    p1evtxdeq.fi
    vtxdun
end
