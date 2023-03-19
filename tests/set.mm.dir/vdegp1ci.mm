include "ciedg.mm"
include "cfv.mm"
include "cpr.mm"
include "cs1.mm"
include "cconcat.mm"
include "co.mm"
include "wceq.mm"
include "prcom.mm"
include "s1eq.mm"
include "ax-mp.mm"
include "oveq2i.mm"
include "eqtri.mm"
include "vdegp1bi.mm"

theorem vdegp1ci
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
  assume vdegp1bi.x: |- X e. V
  assume vdegp1bi.xu: |- X =/= U
  assume vdegp1ci.f: |- ( iEdg ` F ) = ( I ++ <" { X , U } "> )

  disjoint U x
  disjoint V x
  disjoint X x
  disjoint Y x
  assert |- ( ( VtxDeg ` F ) ` U ) = ( P + 1 )

  proof
    vx
    cP
    cU
    cF
    cG
    cI
    cV
    cX
    vdegp1ai.vg
    vdegp1ai.u
    vdegp1ai.i
    vdegp1ai.w
    vdegp1ai.d
    vdegp1ai.vf
    vdegp1bi.x
    vdegp1bi.xu
    cF
    ciedg
    cfv
    cI
    cX
    cU
    cpr
    #
    cs1
    #
    cconcat
    co
    cI
    cU
    cX
    cpr
    #
    cs1
    #
    cconcat
    co
    vdegp1ci.f
    @1
    @3
    cI
    cconcat
    @0
    @2
    wceq
    @1
    @3
    wceq
    cX
    cU
    prcom
    @0
    @2
    s1eq
    ax-mp
    oveq2i
    eqtri
    vdegp1bi
end
