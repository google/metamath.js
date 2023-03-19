include "cc0.mm"
include "c1.mm"
include "cioc.mm"
include "co.mm"
include "wcel.mm"
include "cfv.mm"
include "wceq.mm"
include "cpnf.mm"
include "clog.mm"
include "cneg.mm"
include "cif.mm"
include "cicc.mm"
include "iocssicc.mm"
include "sseli.mm"
include "cv.mm"
include "eqeq1.mm"
include "fveq2.mm"
include "negeqd.mm"
include "ifbieq2d.mm"
include "pnfex.mm"
include "negex.mm"
include "ifex.mm"
include "fvmpt.mm"
include "syl.mm"
include "cr.mm"
include "clt.mm"
include "wbr.mm"
include "cle.mm"
include "cxr.mm"
include "w3a.mm"
include "wb.mm"
include "0xr.mm"
include "1re.mm"
include "elioc2.mm"
include "mp2an.mm"
include "simp2bi.mm"
include "gt0ne0d.mm"
include "neneqd.mm"
include "iffalsed.mm"
include "eqtrd.mm"

theorem xrge0iifcv
  let vx: setvar x
  let cF: class F
  let cX: class X
  let vy: setvar y
  assume xrge0iifhmeo.1: |- F = ( x e. ( 0 [,] 1 ) |-> if ( x = 0 , +oo , -u ( log ` x ) ) )

  disjoint X x
  disjoint x y
  assert |- ( X e. ( 0 (,] 1 ) -> ( F ` X ) = -u ( log ` X ) )

  proof
    cX
    cc0
    c1
    cioc
    co
    #
    wcel
    #
    cX
    cF
    cfv
    #
    cX
    cc0
    wceq
    #
    cpnf
    cX
    clog
    cfv
    #
    cneg
    #
    cif
    #
    @5
    @1
    cX
    cc0
    c1
    cicc
    co
    #
    wcel
    @2
    @6
    wceq
    @0
    @7
    cX
    cc0
    c1
    iocssicc
    sseli
    vx
    cX
    vx
    cv
    #
    cc0
    wceq
    #
    cpnf
    @8
    clog
    cfv
    #
    cneg
    #
    cif
    @6
    @7
    cF
    @8
    cX
    wceq
    #
    @9
    @3
    @11
    @5
    cpnf
    @8
    cX
    cc0
    eqeq1
    @12
    @10
    @4
    @8
    cX
    clog
    fveq2
    negeqd
    ifbieq2d
    xrge0iifhmeo.1
    @3
    cpnf
    @5
    pnfex
    @4
    negex
    ifex
    fvmpt
    syl
    @1
    @3
    cpnf
    @5
    @1
    cX
    cc0
    @1
    cX
    @1
    cX
    cr
    wcel
    #
    cc0
    cX
    clt
    wbr
    #
    cX
    c1
    cle
    wbr
    #
    cc0
    cxr
    wcel
    c1
    cr
    wcel
    @1
    @13
    @14
    @15
    w3a
    wb
    0xr
    1re
    cc0
    c1
    cX
    elioc2
    mp2an
    simp2bi
    gt0ne0d
    neneqd
    iffalsed
    eqtrd
end
