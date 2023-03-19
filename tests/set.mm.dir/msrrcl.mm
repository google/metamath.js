include "cfv.mm"
include "wceq.mm"
include "wcel.mm"
include "wi.mm"
include "msrf.mm"
include "ffvelrni.mm"
include "a1i.mm"
include "eleq1.mm"
include "syl5ibr.mm"
include "wb.mm"
include "wa.mm"
include "fdmi.mm"
include "c0.mm"
include "cvv.mm"
include "cxp.mm"
include "0nelxp.mm"
include "mpstssv.mm"
include "sseli.mm"
include "mto.mm"
include "ndmfvrcl.mm"
include "adantl.mm"
include "biimpa.mm"
include "syl.mm"
include "2thd.mm"
include "ex.mm"
include "pm5.21ndd.mm"

theorem msrrcl
  let cP: class P
  let cR: class R
  let cT: class T
  let cX: class X
  let cY: class Y
  let va: setvar a
  let vh: setvar h
  let vs: setvar s
  let vz: setvar z
  let vd: setvar d
  assume mpstssv.p: |- P = ( mPreSt ` T )
  assume msrf.r: |- R = ( mStRed ` T )


  assert |- ( ( R ` X ) = ( R ` Y ) -> ( X e. P <-> Y e. P ) )

  proof
    cX
    cR
    cfv
    #
    cY
    cR
    cfv
    #
    wceq
    #
    @0
    cP
    wcel
    #
    cX
    cP
    wcel
    #
    cY
    cP
    wcel
    #
    @4
    @3
    wi
    @2
    cP
    cP
    cX
    cR
    cP
    cR
    cT
    mpstssv.p
    msrf.r
    msrf
    #
    ffvelrni
    a1i
    @5
    @3
    @2
    @1
    cP
    wcel
    #
    cP
    cP
    cY
    cR
    @6
    ffvelrni
    @0
    @1
    cP
    eleq1
    #
    syl5ibr
    @2
    @3
    @4
    @5
    wb
    @2
    @3
    wa
    #
    @4
    @5
    @3
    @4
    @2
    cX
    cP
    cR
    cP
    cP
    cR
    @6
    fdmi
    #
    c0
    cP
    wcel
    c0
    cvv
    cvv
    cxp
    #
    cvv
    cxp
    #
    wcel
    @11
    cvv
    0nelxp
    cP
    @12
    c0
    cP
    cT
    mpstssv.p
    mpstssv
    sseli
    mto
    #
    ndmfvrcl
    adantl
    @9
    @7
    @5
    @2
    @3
    @7
    @8
    biimpa
    cY
    cP
    cR
    @10
    @13
    ndmfvrcl
    syl
    2thd
    ex
    pm5.21ndd
end
