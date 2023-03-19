include "c2.mm"
include "cv.mm"
include "cc0.mm"
include "cfzo.mm"
include "co.mm"
include "cima.mm"
include "cres.mm"
include "cop.mm"
include "cvtxdg.mm"
include "cfv.mm"
include "cdvds.mm"
include "wbr.mm"
include "wn.mm"
include "wral.mm"
include "crab.mm"
include "c0.mm"
include "wceq.mm"
include "wcel.mm"
include "wa.mm"
include "cz.mm"
include "2z.mm"
include "dvds0.mm"
include "ax-mp.mm"
include "cvtx.mm"
include "ciedg.mm"
include "cvv.mm"
include "fvex.mm"
include "eqeltri.mm"
include "resex.mm"
include "pm3.2i.mm"
include "opvtxfv.mm"
include "mp1i.mm"
include "eqcomd.mm"
include "eleq2d.mm"
include "biimpa.mm"
include "opiedgfv.mm"
include "fzo0.mm"
include "imaeq2i.mm"
include "ima0.mm"
include "eqtri.mm"
include "reseq2i.mm"
include "res0.mm"
include "syl6eq.mm"
include "adantr.mm"
include "eqid.mm"
include "vtxdg0e.mm"
include "syl2anc.mm"
include "syl5breqr.mm"
include "notnotd.mm"
include "ralrimiva.mm"
include "rabeq0.mm"
include "sylibr.mm"

theorem eupth2lemb
  let wph: wff ph
  let vx: setvar x
  let cP: class P
  let cF: class F
  let cG: class G
  let cI: class I
  let cV: class V
  assume eupth2.v: |- V = ( Vtx ` G )
  assume eupth2.i: |- I = ( iEdg ` G )
  assume eupth2.g: |- ( ph -> G e. UPGraph )
  assume eupth2.f: |- ( ph -> Fun I )
  assume eupth2.p: |- ( ph -> F ( EulerPaths ` G ) P )

  disjoint ph x
  assert |- ( ph -> { x e. V | -. 2 || ( ( VtxDeg ` <. V , ( I |` ( F " ( 0 ..^ 0 ) ) ) >. ) ` x ) } = (/) )

  proof
    wph
    c2
    vx
    cv
    #
    cV
    cI
    cF
    cc0
    cc0
    cfzo
    co
    #
    cima
    #
    cres
    #
    cop
    #
    cvtxdg
    cfv
    cfv
    #
    cdvds
    wbr
    #
    wn
    #
    wn
    #
    vx
    cV
    wral
    @7
    vx
    cV
    crab
    c0
    wceq
    wph
    @8
    vx
    cV
    wph
    @0
    cV
    wcel
    #
    wa
    #
    @6
    @10
    c2
    cc0
    @5
    cdvds
    c2
    cz
    wcel
    c2
    cc0
    cdvds
    wbr
    2z
    c2
    dvds0
    ax-mp
    @10
    @0
    @4
    cvtx
    cfv
    #
    wcel
    #
    @4
    ciedg
    cfv
    #
    c0
    wceq
    #
    @5
    cc0
    wceq
    wph
    @9
    @12
    wph
    cV
    @11
    @0
    wph
    @11
    cV
    cV
    cvv
    wcel
    #
    @3
    cvv
    wcel
    #
    wa
    #
    @11
    cV
    wceq
    wph
    @15
    @16
    cV
    cG
    cvtx
    cfv
    cvv
    eupth2.v
    cG
    cvtx
    fvex
    eqeltri
    cI
    @2
    cI
    cG
    ciedg
    cfv
    cvv
    eupth2.i
    cG
    ciedg
    fvex
    eqeltri
    resex
    pm3.2i
    #
    @3
    cV
    cvv
    cvv
    opvtxfv
    mp1i
    eqcomd
    eleq2d
    biimpa
    wph
    @14
    @9
    wph
    @13
    @3
    c0
    @17
    @13
    @3
    wceq
    wph
    @18
    @3
    cV
    cvv
    cvv
    opiedgfv
    mp1i
    @3
    cI
    c0
    cres
    c0
    @2
    c0
    cI
    @2
    cF
    c0
    cima
    c0
    @1
    c0
    cF
    cc0
    fzo0
    imaeq2i
    cF
    ima0
    eqtri
    reseq2i
    cI
    res0
    eqtri
    syl6eq
    adantr
    @0
    @4
    @13
    @11
    @11
    eqid
    @13
    eqid
    vtxdg0e
    syl2anc
    syl5breqr
    notnotd
    ralrimiva
    @7
    vx
    cV
    rabeq0
    sylibr
end
