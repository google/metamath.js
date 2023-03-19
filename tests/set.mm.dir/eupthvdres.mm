include "cvv.mm"
include "wcel.mm"
include "cc0.mm"
include "chash.mm"
include "cfv.mm"
include "cfzo.mm"
include "co.mm"
include "cima.mm"
include "cres.mm"
include "cop.mm"
include "opex.mm"
include "eqeltri.mm"
include "a1i.mm"
include "cvtx.mm"
include "fveq2i.mm"
include "wa.mm"
include "wceq.mm"
include "fvex.mm"
include "ciedg.mm"
include "resex.mm"
include "pm3.2i.mm"
include "opvtxfv.mm"
include "syl.mm"
include "syl5eq.mm"
include "syl6eq.mm"
include "cdm.mm"
include "opiedgfv.mm"
include "wf1o.mm"
include "wfo.mm"
include "ceupth.mm"
include "wbr.mm"
include "eupthf1o.mm"
include "f1ofo.mm"
include "foima.mm"
include "3syl.mm"
include "reseq2d.mm"
include "wfn.mm"
include "wfun.mm"
include "funfn.mm"
include "sylib.mm"
include "fnresdm.mm"
include "3eqtrd.mm"
include "vtxdeqd.mm"

theorem eupthvdres
  let wph: wff ph
  let cP: class P
  let cF: class F
  let cG: class G
  let cH: class H
  let cI: class I
  let cV: class V
  let cW: class W
  assume eupthvdres.v: |- V = ( Vtx ` G )
  assume eupthvdres.i: |- I = ( iEdg ` G )
  assume eupthvdres.g: |- ( ph -> G e. W )
  assume eupthvdres.f: |- ( ph -> Fun I )
  assume eupthvdres.p: |- ( ph -> F ( EulerPaths ` G ) P )
  assume eupthvdres.h: |- H = <. V , ( I |` ( F " ( 0 ..^ ( # ` F ) ) ) ) >.


  assert |- ( ph -> ( VtxDeg ` H ) = ( VtxDeg ` G ) )

  proof
    wph
    cG
    cH
    cW
    cvv
    eupthvdres.g
    cH
    cvv
    wcel
    wph
    cH
    cV
    cI
    cF
    cc0
    cF
    chash
    cfv
    cfzo
    co
    #
    cima
    #
    cres
    #
    cop
    #
    cvv
    eupthvdres.h
    cV
    @2
    opex
    eqeltri
    a1i
    wph
    cH
    cvtx
    cfv
    #
    cV
    cG
    cvtx
    cfv
    #
    wph
    @4
    @3
    cvtx
    cfv
    #
    cV
    cH
    @3
    cvtx
    eupthvdres.h
    fveq2i
    wph
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
    @6
    cV
    wceq
    @9
    wph
    @7
    @8
    cV
    @5
    cvv
    eupthvdres.v
    cG
    cvtx
    fvex
    eqeltri
    cI
    @1
    cI
    cG
    ciedg
    cfv
    #
    cvv
    eupthvdres.i
    cG
    ciedg
    fvex
    eqeltri
    resex
    pm3.2i
    a1i
    #
    @2
    cV
    cvv
    cvv
    opvtxfv
    syl
    syl5eq
    eupthvdres.v
    syl6eq
    wph
    cH
    ciedg
    cfv
    #
    cI
    @10
    wph
    @12
    @2
    cI
    cI
    cdm
    #
    cres
    #
    cI
    wph
    @12
    @3
    ciedg
    cfv
    #
    @2
    cH
    @3
    ciedg
    eupthvdres.h
    fveq2i
    wph
    @9
    @15
    @2
    wceq
    @11
    @2
    cV
    cvv
    cvv
    opiedgfv
    syl
    syl5eq
    wph
    @1
    @13
    cI
    wph
    @0
    @13
    cF
    wf1o
    #
    @0
    @13
    cF
    wfo
    @1
    @13
    wceq
    wph
    cF
    cP
    cG
    ceupth
    cfv
    wbr
    @16
    eupthvdres.p
    cP
    cF
    cG
    cI
    eupthvdres.i
    eupthf1o
    syl
    @0
    @13
    cF
    f1ofo
    @0
    @13
    cF
    foima
    3syl
    reseq2d
    wph
    cI
    @13
    wfn
    #
    @14
    cI
    wceq
    wph
    cI
    wfun
    @17
    eupthvdres.f
    cI
    funfn
    sylib
    @13
    cI
    fnresdm
    syl
    3eqtrd
    eupthvdres.i
    syl6eq
    vtxdeqd
end
