include "wcel.mm"
include "cv.mm"
include "cvtx.mm"
include "cfv.mm"
include "wceq.mm"
include "ciedg.mm"
include "wa.mm"
include "wi.mm"
include "wal.mm"
include "wsbc.mm"
include "cbs.mm"
include "c0.mm"
include "csn.mm"
include "cdif.mm"
include "wfun.mm"
include "c2.mm"
include "cdm.mm"
include "chash.mm"
include "cle.mm"
include "wbr.mm"
include "funvtxdmge2val.mm"
include "syl2anc.mm"
include "eqtrd.mm"
include "cedgf.mm"
include "funiedgdmge2val.mm"
include "jca.mm"
include "nfcv.mm"
include "nfv.mm"
include "nfsbc1v.mm"
include "nfim.mm"
include "fveq2.mm"
include "eqeq1d.mm"
include "anbi12d.mm"
include "sbceq1a.mm"
include "imbi12d.mm"
include "spcgf.mm"
include "syl3c.mm"

theorem grstructd
  let wph: wff ph
  let wps: wff ps
  let cS: class S
  let cU: class U
  let vg: setvar g
  let cE: class E
  let cV: class V
  let cW: class W
  let cX: class X
  assume gropd.g: |- ( ph -> A. g ( ( ( Vtx ` g ) = V /\ ( iEdg ` g ) = E ) -> ps ) )
  assume gropd.v: |- ( ph -> V e. U )
  assume gropd.e: |- ( ph -> E e. W )
  assume grstructd.s: |- ( ph -> S e. X )
  assume grstructd.f: |- ( ph -> Fun ( S \ { (/) } ) )
  assume grstructd.d: |- ( ph -> 2 <_ ( # ` dom S ) )
  assume grstructd.b: |- ( ph -> ( Base ` S ) = V )
  assume grstructd.e: |- ( ph -> ( .ef ` S ) = E )

  disjoint E g
  disjoint V g
  disjoint g ph
  disjoint S g
  assert |- ( ph -> [. S / g ]. ps )

  proof
    wph
    cS
    cX
    wcel
    vg
    cv
    #
    cvtx
    cfv
    #
    cV
    wceq
    #
    @0
    ciedg
    cfv
    #
    cE
    wceq
    #
    wa
    #
    wps
    wi
    #
    vg
    wal
    cS
    cvtx
    cfv
    #
    cV
    wceq
    #
    cS
    ciedg
    cfv
    #
    cE
    wceq
    #
    wa
    #
    wps
    vg
    cS
    wsbc
    #
    grstructd.s
    gropd.g
    wph
    @8
    @10
    wph
    @7
    cS
    cbs
    cfv
    #
    cV
    wph
    cS
    c0
    csn
    cdif
    wfun
    #
    c2
    cS
    cdm
    chash
    cfv
    cle
    wbr
    #
    @7
    @13
    wceq
    grstructd.f
    grstructd.d
    cS
    funvtxdmge2val
    syl2anc
    grstructd.b
    eqtrd
    wph
    @9
    cS
    cedgf
    cfv
    #
    cE
    wph
    @14
    @15
    @9
    @16
    wceq
    grstructd.f
    grstructd.d
    cS
    funiedgdmge2val
    syl2anc
    grstructd.e
    eqtrd
    jca
    @6
    @11
    @12
    wi
    vg
    cS
    cX
    vg
    cS
    nfcv
    @11
    @12
    vg
    @11
    vg
    nfv
    wps
    vg
    cS
    nfsbc1v
    nfim
    @0
    cS
    wceq
    #
    @5
    @11
    wps
    @12
    @17
    @2
    @8
    @4
    @10
    @17
    @1
    @7
    cV
    @0
    cS
    cvtx
    fveq2
    eqeq1d
    @17
    @3
    @9
    cE
    @0
    cS
    ciedg
    fveq2
    eqeq1d
    anbi12d
    wps
    vg
    cS
    sbceq1a
    imbi12d
    spcgf
    syl3c
end
