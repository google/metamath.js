include "cop.mm"
include "cvv.mm"
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
include "opex.mm"
include "a1i.mm"
include "opvtxfv.mm"
include "opiedgfv.mm"
include "jca.mm"
include "syl2anc.mm"
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

theorem gropd
  let wph: wff ph
  let wps: wff ps
  let cU: class U
  let vg: setvar g
  let cE: class E
  let cV: class V
  let cW: class W
  assume gropd.g: |- ( ph -> A. g ( ( ( Vtx ` g ) = V /\ ( iEdg ` g ) = E ) -> ps ) )
  assume gropd.v: |- ( ph -> V e. U )
  assume gropd.e: |- ( ph -> E e. W )

  disjoint E g
  disjoint V g
  disjoint g ph
  assert |- ( ph -> [. <. V , E >. / g ]. ps )

  proof
    wph
    cV
    cE
    cop
    #
    cvv
    wcel
    #
    vg
    cv
    #
    cvtx
    cfv
    #
    cV
    wceq
    #
    @2
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
    @0
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
    vg
    @0
    wsbc
    #
    @1
    wph
    cV
    cE
    opex
    a1i
    gropd.g
    wph
    cV
    cU
    wcel
    #
    cE
    cW
    wcel
    #
    @13
    gropd.v
    gropd.e
    @15
    @16
    wa
    @10
    @12
    cE
    cV
    cU
    cW
    opvtxfv
    cE
    cV
    cU
    cW
    opiedgfv
    jca
    syl2anc
    @8
    @13
    @14
    wi
    vg
    @0
    cvv
    vg
    @0
    nfcv
    @13
    @14
    vg
    @13
    vg
    nfv
    wps
    vg
    @0
    nfsbc1v
    nfim
    @2
    @0
    wceq
    #
    @7
    @13
    wps
    @14
    @17
    @4
    @10
    @6
    @12
    @17
    @3
    @9
    cV
    @2
    @0
    cvtx
    fveq2
    eqeq1d
    @17
    @5
    @11
    cE
    @2
    @0
    ciedg
    fveq2
    eqeq1d
    anbi12d
    wps
    vg
    @0
    sbceq1a
    imbi12d
    spcgf
    syl3c
end
