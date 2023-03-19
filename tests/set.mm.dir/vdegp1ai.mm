include "cvtxdg.mm"
include "cfv.mm"
include "cpr.mm"
include "cvv.mm"
include "wcel.mm"
include "wceq.mm"
include "prex.mm"
include "chash.mm"
include "cv.mm"
include "c2.mm"
include "cle.mm"
include "wbr.mm"
include "cpw.mm"
include "c0.mm"
include "csn.mm"
include "cdif.mm"
include "crab.mm"
include "cword.mm"
include "wfun.mm"
include "cc0.mm"
include "cfzo.mm"
include "co.mm"
include "wf.mm"
include "wrdf.mm"
include "ffun.mm"
include "syl.mm"
include "mp1i.mm"
include "cvtx.mm"
include "a1i.mm"
include "ciedg.mm"
include "cs1.mm"
include "cconcat.mm"
include "cop.mm"
include "cun.mm"
include "wrdv.mm"
include "ax-mp.mm"
include "cats1un.mm"
include "mpan.mm"
include "syl5eq.mm"
include "fvexd.mm"
include "cdm.mm"
include "wnel.mm"
include "wrdlndm.mm"
include "id.mm"
include "necomi.mm"
include "prneli.mm"
include "p1evtxdeq.mm"
include "eqtri.mm"

theorem vdegp1ai
  let vx: setvar x
  let cP: class P
  let cU: class U
  let cF: class F
  let cG: class G
  let cI: class I
  let cV: class V
  let cX: class X
  let cY: class Y
  assume vdegp1ai.vg: |- V = ( Vtx ` G )
  assume vdegp1ai.u: |- U e. V
  assume vdegp1ai.i: |- I = ( iEdg ` G )
  assume vdegp1ai.w: |- I e. Word { x e. ( ~P V \ { (/) } ) | ( # ` x ) <_ 2 }
  assume vdegp1ai.d: |- ( ( VtxDeg ` G ) ` U ) = P
  assume vdegp1ai.vf: |- ( Vtx ` F ) = V
  assume vdegp1ai.x: |- X e. V
  assume vdegp1ai.xu: |- X =/= U
  assume vdegp1ai.y: |- Y e. V
  assume vdegp1ai.yu: |- Y =/= U
  assume vdegp1ai.f: |- ( iEdg ` F ) = ( I ++ <" { X , Y } "> )

  disjoint U x
  disjoint V x
  disjoint X x
  disjoint Y x
  assert |- ( ( VtxDeg ` F ) ` U ) = P

  proof
    cU
    cF
    cvtxdg
    cfv
    cfv
    #
    cU
    cG
    cvtxdg
    cfv
    cfv
    #
    cP
    cX
    cY
    cpr
    #
    cvv
    wcel
    #
    @0
    @1
    wceq
    cX
    cY
    prex
    @3
    cU
    @2
    cF
    cG
    cI
    cI
    chash
    cfv
    #
    cV
    cvv
    cvv
    vdegp1ai.vg
    vdegp1ai.i
    cI
    vx
    cv
    chash
    cfv
    c2
    cle
    wbr
    vx
    cV
    cpw
    c0
    csn
    cdif
    crab
    #
    cword
    wcel
    #
    cI
    wfun
    #
    @3
    vdegp1ai.w
    @6
    cc0
    @4
    cfzo
    co
    #
    @5
    cI
    wf
    @7
    @5
    cI
    wrdf
    @8
    @5
    cI
    ffun
    syl
    mp1i
    cF
    cvtx
    cfv
    cV
    wceq
    @3
    vdegp1ai.vf
    a1i
    @3
    cF
    ciedg
    cfv
    cI
    @2
    cs1
    cconcat
    co
    #
    cI
    @4
    @2
    cop
    csn
    cun
    #
    vdegp1ai.f
    cI
    cvv
    cword
    wcel
    #
    @3
    @9
    @10
    wceq
    @6
    @11
    vdegp1ai.w
    @5
    cI
    wrdv
    ax-mp
    cI
    @2
    cvv
    cats1un
    mpan
    syl5eq
    @3
    cI
    chash
    fvexd
    @6
    @4
    cI
    cdm
    wnel
    @3
    vdegp1ai.w
    @5
    cI
    wrdlndm
    mp1i
    cU
    cV
    wcel
    @3
    vdegp1ai.u
    a1i
    @3
    id
    cU
    @2
    wnel
    @3
    cU
    cX
    cY
    cX
    cU
    vdegp1ai.xu
    necomi
    cY
    cU
    vdegp1ai.yu
    necomi
    prneli
    a1i
    p1evtxdeq
    ax-mp
    vdegp1ai.d
    eqtri
end
