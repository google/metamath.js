include "cnv.mm"
include "wcel.mm"
include "wa.mm"
include "co.mm"
include "cc0.mm"
include "wceq.mm"
include "cnmcv.mm"
include "cfv.mm"
include "c2.mm"
include "cexp.mm"
include "eqid.mm"
include "ipidsq.mm"
include "eqeq1d.mm"
include "cc.mm"
include "wb.mm"
include "nvcl.mm"
include "recnd.mm"
include "sqeq0.mm"
include "syl.mm"
include "nvz.mm"
include "3bitrd.mm"

theorem ipz
  let cA: class A
  let cP: class P
  let cU: class U
  let cX: class X
  let cZ: class Z
  assume dip0r.1: |- X = ( BaseSet ` U )
  assume dip0r.5: |- Z = ( 0vec ` U )
  assume dip0r.7: |- P = ( .iOLD ` U )


  assert |- ( ( U e. NrmCVec /\ A e. X ) -> ( ( A P A ) = 0 <-> A = Z ) )

  proof
    cU
    cnv
    wcel
    cA
    cX
    wcel
    wa
    #
    cA
    cA
    cP
    co
    #
    cc0
    wceq
    cA
    cU
    cnmcv
    cfv
    #
    cfv
    #
    c2
    cexp
    co
    #
    cc0
    wceq
    #
    @3
    cc0
    wceq
    #
    cA
    cZ
    wceq
    @0
    @1
    @4
    cc0
    cA
    cP
    cU
    @2
    cX
    dip0r.1
    @2
    eqid
    #
    dip0r.7
    ipidsq
    eqeq1d
    @0
    @3
    cc
    wcel
    @5
    @6
    wb
    @0
    @3
    cA
    cU
    @2
    cX
    dip0r.1
    @7
    nvcl
    recnd
    @3
    sqeq0
    syl
    cA
    cU
    @2
    cX
    cZ
    dip0r.1
    dip0r.5
    @7
    nvz
    3bitrd
end
