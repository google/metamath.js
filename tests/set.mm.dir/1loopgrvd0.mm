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
include "csn.mm"
include "cop.mm"
include "eldifbd.mm"
include "cvv.mm"
include "snex.mm"
include "fvsng.mm"
include "sylancl.mm"
include "eleq2d.mm"
include "mtbird.mm"
include "dmeqd.mm"
include "dmsnopg.mm"
include "mp1i.mm"
include "eqtrd.mm"
include "fveq1d.mm"
include "rexeqbidv.mm"
include "wb.mm"
include "fveq2.mm"
include "rexsng.mm"
include "syl.mm"
include "bitrd.mm"
include "cvtx.mm"
include "eldifad.mm"
include "mpbird.mm"
include "eqid.mm"
include "vtxd0nedgb.mm"

theorem 1loopgrvd0
  let wph: wff ph
  let cA: class A
  let cG: class G
  let cK: class K
  let cN: class N
  let cV: class V
  let cX: class X
  let vv: setvar v
  let va: setvar a
  let ve: setvar e
  let vi: setvar i
  assume 1loopgruspgr.v: |- ( ph -> ( Vtx ` G ) = V )
  assume 1loopgruspgr.a: |- ( ph -> A e. X )
  assume 1loopgruspgr.n: |- ( ph -> N e. V )
  assume 1loopgruspgr.i: |- ( ph -> ( iEdg ` G ) = { <. A , { N } >. } )
  assume 1loopgrvd0.k: |- ( ph -> K e. ( V \ { N } ) )


  assert |- ( ph -> ( ( VtxDeg ` G ) ` K ) = 0 )

  proof
    wph
    cK
    cG
    cvtxdg
    cfv
    #
    cfv
    cc0
    wceq
    #
    cK
    vi
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
    vi
    @3
    cdm
    #
    wrex
    #
    wn
    #
    wph
    @7
    cK
    cA
    cA
    cN
    csn
    #
    cop
    csn
    #
    cfv
    #
    wcel
    #
    wph
    @12
    cK
    @9
    wcel
    wph
    cK
    cV
    @9
    1loopgrvd0.k
    eldifbd
    wph
    @11
    @9
    cK
    wph
    cA
    cX
    wcel
    #
    @9
    cvv
    wcel
    #
    @11
    @9
    wceq
    1loopgruspgr.a
    cN
    snex
    #
    cA
    @9
    cX
    cvv
    fvsng
    sylancl
    eleq2d
    mtbird
    wph
    @7
    cK
    @2
    @10
    cfv
    #
    wcel
    #
    vi
    cA
    csn
    #
    wrex
    #
    @12
    wph
    @5
    @17
    vi
    @6
    @18
    wph
    @6
    @10
    cdm
    #
    @18
    wph
    @3
    @10
    1loopgruspgr.i
    dmeqd
    @14
    @20
    @18
    wceq
    wph
    @15
    cA
    @9
    cvv
    dmsnopg
    mp1i
    eqtrd
    wph
    @4
    @16
    cK
    wph
    @2
    @3
    @10
    1loopgruspgr.i
    fveq1d
    eleq2d
    rexeqbidv
    wph
    @13
    @19
    @12
    wb
    1loopgruspgr.a
    @17
    @12
    vi
    cA
    cX
    @2
    cA
    wceq
    @16
    @11
    cK
    @2
    cA
    @10
    fveq2
    eleq2d
    rexsng
    syl
    bitrd
    mtbird
    wph
    cK
    cG
    cvtx
    cfv
    #
    wcel
    #
    @1
    @8
    wb
    wph
    @22
    cK
    cV
    wcel
    wph
    cK
    cV
    @9
    1loopgrvd0.k
    eldifad
    wph
    @21
    cV
    cK
    1loopgruspgr.v
    eleq2d
    mpbird
    @0
    cK
    vi
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
