include "cvtxdg.mm"
include "cfv.mm"
include "cc0.mm"
include "wceq.mm"
include "cv.mm"
include "ciedg.mm"
include "wcel.mm"
include "cdm.mm"
include "wrex.mm"
include "wn.mm"
include "wral.mm"
include "csn.mm"
include "wnel.mm"
include "df-nel.mm"
include "sylib.mm"
include "cop.mm"
include "fveq1d.mm"
include "fvsng.mm"
include "syl2anc.mm"
include "eqtrd.mm"
include "neleqtrrd.mm"
include "wb.mm"
include "fveq2.mm"
include "eleq2d.mm"
include "notbid.mm"
include "ralsng.mm"
include "syl.mm"
include "mpbird.mm"
include "dmeqd.mm"
include "dmsnopg.mm"
include "raleqdv.mm"
include "ralnex.mm"
include "cvtx.mm"
include "eqid.mm"
include "vtxd0nedgb.mm"

theorem 1hevtxdg0
  let wph: wff ph
  let cA: class A
  let cD: class D
  let cE: class E
  let cG: class G
  let cV: class V
  let cX: class X
  let cY: class Y
  let vx: setvar x
  assume 1hevtxdg0.i: |- ( ph -> ( iEdg ` G ) = { <. A , E >. } )
  assume 1hevtxdg0.v: |- ( ph -> ( Vtx ` G ) = V )
  assume 1hevtxdg0.a: |- ( ph -> A e. X )
  assume 1hevtxdg0.d: |- ( ph -> D e. V )
  assume 1hevtxdg0.e: |- ( ph -> E e. Y )
  assume 1hevtxdg0.n: |- ( ph -> D e/ E )


  assert |- ( ph -> ( ( VtxDeg ` G ) ` D ) = 0 )

  proof
    wph
    cD
    cG
    cvtxdg
    cfv
    #
    cfv
    cc0
    wceq
    #
    cD
    vx
    cv
    #
    cG
    ciedg
    cfv
    #
    cfv
    #
    wcel
    #
    vx
    @3
    cdm
    #
    wrex
    wn
    #
    wph
    @5
    wn
    #
    vx
    @6
    wral
    #
    @7
    wph
    @9
    @8
    vx
    cA
    csn
    #
    wral
    #
    wph
    @11
    cD
    cA
    @3
    cfv
    #
    wcel
    #
    wn
    #
    wph
    @12
    cE
    cD
    wph
    cD
    cE
    wnel
    cD
    cE
    wcel
    wn
    1hevtxdg0.n
    cD
    cE
    df-nel
    sylib
    wph
    @12
    cA
    cA
    cE
    cop
    csn
    #
    cfv
    #
    cE
    wph
    cA
    @3
    @15
    1hevtxdg0.i
    fveq1d
    wph
    cA
    cX
    wcel
    #
    cE
    cY
    wcel
    #
    @16
    cE
    wceq
    1hevtxdg0.a
    1hevtxdg0.e
    cA
    cE
    cX
    cY
    fvsng
    syl2anc
    eqtrd
    neleqtrrd
    wph
    @17
    @11
    @14
    wb
    1hevtxdg0.a
    @8
    @14
    vx
    cA
    cX
    @2
    cA
    wceq
    #
    @5
    @13
    @19
    @4
    @12
    cD
    @2
    cA
    @3
    fveq2
    eleq2d
    notbid
    ralsng
    syl
    mpbird
    wph
    @8
    vx
    @6
    @10
    wph
    @6
    @15
    cdm
    #
    @10
    wph
    @3
    @15
    1hevtxdg0.i
    dmeqd
    wph
    @18
    @20
    @10
    wceq
    1hevtxdg0.e
    cA
    cE
    cY
    dmsnopg
    syl
    eqtrd
    raleqdv
    mpbird
    @5
    vx
    @6
    ralnex
    sylib
    wph
    cD
    cG
    cvtx
    cfv
    #
    wcel
    #
    @1
    @7
    wb
    wph
    @22
    cD
    cV
    wcel
    1hevtxdg0.d
    wph
    @21
    cV
    cD
    1hevtxdg0.v
    eleq2d
    mpbird
    @0
    cD
    vx
    cG
    @3
    @21
    @21
    eqid
    @3
    eqid
    @0
    eqid
    vtxd0nedgb
    syl
    mpbird
end
