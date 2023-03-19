include "ccph.mm"
include "wcel.mm"
include "w3a.mm"
include "co.mm"
include "cabs.mm"
include "cfv.mm"
include "ctch.mm"
include "cnm.mm"
include "cmul.mm"
include "cle.mm"
include "cdiv.mm"
include "csca.mm"
include "cbs.mm"
include "eqid.mm"
include "cphl.mm"
include "simp1.mm"
include "cphphl.mm"
include "syl.mm"
include "ccnfld.mm"
include "cress.mm"
include "wceq.mm"
include "cphsca.mm"
include "cv.mm"
include "cr.mm"
include "cc0.mm"
include "wbr.mm"
include "csqrt.mm"
include "cphsqrtcl.mm"
include "sylan.mm"
include "ipge0.mm"
include "simp2.mm"
include "simp3.mm"
include "ipcau2.mm"
include "cphtchnm.mm"
include "fveq1d.mm"
include "oveq12d.mm"
include "breqtrrd.mm"

theorem ipcau
  let c.xi: class .,
  let cN: class N
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  let vx: setvar x
  assume ipcau.v: |- V = ( Base ` W )
  assume ipcau.h: |- ., = ( .i ` W )
  assume ipcau.n: |- N = ( norm ` W )


  assert |- ( ( W e. CPreHil /\ X e. V /\ Y e. V ) -> ( abs ` ( X ., Y ) ) <_ ( ( N ` X ) x. ( N ` Y ) ) )

  proof
    cW
    ccph
    wcel
    #
    cX
    cV
    wcel
    #
    cY
    cV
    wcel
    #
    w3a
    #
    cX
    cY
    c.xi
    co
    cabs
    cfv
    cX
    cW
    ctch
    cfv
    #
    cnm
    cfv
    #
    cfv
    #
    cY
    @5
    cfv
    #
    cmul
    co
    cX
    cN
    cfv
    #
    cY
    cN
    cfv
    #
    cmul
    co
    cle
    @3
    vx
    cY
    cX
    c.xi
    co
    cY
    cY
    c.xi
    co
    cdiv
    co
    #
    cW
    csca
    cfv
    #
    @4
    c.xi
    @11
    cbs
    cfv
    #
    @5
    cV
    cW
    cX
    cY
    @4
    eqid
    #
    ipcau.v
    @11
    eqid
    #
    @3
    @0
    cW
    cphl
    wcel
    @0
    @1
    @2
    simp1
    #
    cW
    cphphl
    syl
    @3
    @0
    @11
    ccnfld
    @12
    cress
    co
    wceq
    @15
    @11
    @12
    cW
    @14
    @12
    eqid
    #
    cphsca
    syl
    ipcau.h
    @3
    @0
    vx
    cv
    #
    @12
    wcel
    @17
    cr
    wcel
    cc0
    @17
    cle
    wbr
    w3a
    @17
    csqrt
    cfv
    @12
    wcel
    @15
    @17
    @11
    @12
    cW
    @14
    @16
    cphsqrtcl
    sylan
    @3
    @0
    @17
    cV
    wcel
    cc0
    @17
    @17
    c.xi
    co
    cle
    wbr
    @15
    @17
    c.xi
    cV
    cW
    ipcau.v
    ipcau.h
    ipge0
    sylan
    @16
    @5
    eqid
    @10
    eqid
    @0
    @1
    @2
    simp2
    @0
    @1
    @2
    simp3
    ipcau2
    @3
    @8
    @6
    @9
    @7
    cmul
    @3
    cX
    cN
    @5
    @3
    @0
    cN
    @5
    wceq
    @15
    @4
    cN
    cW
    @13
    ipcau.n
    cphtchnm
    syl
    #
    fveq1d
    @3
    cY
    cN
    @5
    @18
    fveq1d
    oveq12d
    breqtrrd
end
