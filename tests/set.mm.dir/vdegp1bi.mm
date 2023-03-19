include "cvtxdg.mm"
include "cfv.mm"
include "c1.mm"
include "cxad.mm"
include "co.mm"
include "caddc.mm"
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
include "wrdf.mm"
include "ffund.mm"
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
include "wa.mm"
include "pm3.2i.mm"
include "prelpwi.mm"
include "prid1g.mm"
include "wne.mm"
include "necomi.mm"
include "wb.mm"
include "hashprg.mm"
include "mp2an.mm"
include "mpbi.mm"
include "eqcomi.mm"
include "2re.mm"
include "eqlei.mm"
include "p1evtxdp1.mm"
include "cr.mm"
include "cfn.mm"
include "cn0.mm"
include "fzofi.mm"
include "wrddm.mm"
include "vtxdgfisnn0.mm"
include "nn0rei.mm"
include "1re.mm"
include "rexadd.mm"
include "oveq1i.mm"
include "3eqtri.mm"

theorem vdegp1bi
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
  assume vdegp1bi.f: |- ( iEdg ` F ) = ( I ++ <" { U , X } "> )

  disjoint U x
  disjoint V x
  disjoint X x
  disjoint Y x
  assert |- ( ( VtxDeg ` F ) ` U ) = ( P + 1 )

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
    c1
    cxad
    co
    #
    @1
    c1
    caddc
    co
    #
    cP
    c1
    caddc
    co
    cU
    cX
    cpr
    #
    cvv
    wcel
    #
    @0
    @2
    wceq
    cU
    cX
    prex
    @5
    cU
    @4
    cF
    cG
    cI
    cI
    chash
    cfv
    #
    cV
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
    #
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
    @5
    vdegp1ai.w
    @9
    cc0
    @6
    cfzo
    co
    #
    @8
    cI
    @8
    cI
    wrdf
    ffund
    mp1i
    cF
    cvtx
    cfv
    cV
    wceq
    @5
    vdegp1ai.vf
    a1i
    @5
    cF
    ciedg
    cfv
    cI
    @4
    cs1
    cconcat
    co
    #
    cI
    @6
    @4
    cop
    csn
    cun
    #
    vdegp1bi.f
    cI
    cvv
    cword
    wcel
    #
    @5
    @11
    @12
    wceq
    @9
    @13
    vdegp1ai.w
    @8
    cI
    wrdv
    ax-mp
    cI
    @4
    cvv
    cats1un
    mpan
    syl5eq
    @5
    cI
    chash
    fvexd
    @9
    @6
    cI
    cdm
    #
    wnel
    @5
    vdegp1ai.w
    @8
    cI
    wrdlndm
    mp1i
    cU
    cV
    wcel
    #
    @5
    vdegp1ai.u
    a1i
    @15
    cX
    cV
    wcel
    #
    wa
    @4
    @7
    wcel
    @5
    @15
    @16
    vdegp1ai.u
    vdegp1bi.x
    pm3.2i
    cU
    cX
    cV
    prelpwi
    mp1i
    @15
    cU
    @4
    wcel
    @5
    vdegp1ai.u
    cU
    cX
    cV
    prid1g
    mp1i
    c2
    @4
    chash
    cfv
    #
    wceq
    c2
    @17
    cle
    wbr
    @5
    @17
    c2
    cU
    cX
    wne
    #
    @17
    c2
    wceq
    #
    cX
    cU
    vdegp1bi.xu
    necomi
    @15
    @16
    @18
    @19
    wb
    vdegp1ai.u
    vdegp1bi.x
    cU
    cX
    cV
    cV
    hashprg
    mp2an
    mpbi
    eqcomi
    c2
    @17
    2re
    eqlei
    mp1i
    p1evtxdp1
    ax-mp
    @1
    cr
    wcel
    c1
    cr
    wcel
    @2
    @3
    wceq
    @1
    @10
    cfn
    wcel
    @15
    @1
    cn0
    wcel
    cc0
    @6
    fzofi
    vdegp1ai.u
    @10
    cU
    cG
    cI
    cV
    vdegp1ai.vg
    vdegp1ai.i
    @14
    @10
    @9
    @14
    @10
    wceq
    vdegp1ai.w
    @8
    cI
    wrddm
    ax-mp
    eqcomi
    vtxdgfisnn0
    mp2an
    nn0rei
    1re
    @1
    c1
    rexadd
    mp2an
    @1
    cP
    c1
    caddc
    vdegp1ai.d
    oveq1i
    3eqtri
end
