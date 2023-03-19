include "wfr.mm"
include "wcel.mm"
include "cpred.mm"
include "wn.mm"
include "wa.mm"
include "wbr.mm"
include "frirr.mm"
include "wb.mm"
include "elpredg.mm"
include "anidms.mm"
include "notbid.mm"
include "syl5ibr.mm"
include "expd.mm"
include "pm2.43b.mm"
include "predel.mm"
include "con3i.mm"
include "pm2.61d1.mm"

theorem predfrirr
  let cA: class A
  let cR: class R
  let cX: class X


  assert |- ( R Fr A -> -. X e. Pred ( R , A , X ) )

  proof
    cA
    cR
    wfr
    #
    cX
    cA
    wcel
    #
    cX
    cA
    cR
    cX
    cpred
    wcel
    #
    wn
    #
    @0
    @1
    @3
    @1
    @0
    @1
    @3
    @0
    @1
    wa
    @3
    @1
    cX
    cX
    cR
    wbr
    #
    wn
    cA
    cX
    cR
    frirr
    @1
    @2
    @4
    @1
    @2
    @4
    wb
    cA
    cA
    cR
    cX
    cX
    elpredg
    anidms
    notbid
    syl5ibr
    expd
    pm2.43b
    @2
    @1
    cA
    cR
    cX
    cX
    predel
    con3i
    pm2.61d1
end
