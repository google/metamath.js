include "cc0.mm"
include "cpnf.mm"
include "cicc.mm"
include "co.mm"
include "wcel.mm"
include "cmnf.mm"
include "wn.mm"
include "wceq.mm"
include "cle.mm"
include "wbr.mm"
include "cxr.mm"
include "w3a.mm"
include "clt.mm"
include "mnflt0.mm"
include "wb.mm"
include "mnfxr.mm"
include "0xr.mm"
include "xrltnle.mm"
include "mp2an.mm"
include "mpbi.mm"
include "simp2.mm"
include "con3i.mm"
include "pnfxr.mm"
include "elicc1.mm"
include "biimpi.mm"
include "mp2b.mm"
include "nelneq.mm"
include "mpan2.mm"
include "neqned.mm"

theorem xrge0neqmnf
  let cA: class A


  assert |- ( A e. ( 0 [,] +oo ) -> A =/= -oo )

  proof
    cA
    cc0
    cpnf
    cicc
    co
    #
    wcel
    #
    cA
    cmnf
    @1
    cmnf
    @0
    wcel
    #
    wn
    #
    cA
    cmnf
    wceq
    wn
    cc0
    cmnf
    cle
    wbr
    #
    wn
    #
    cmnf
    cxr
    wcel
    #
    @4
    cmnf
    cpnf
    cle
    wbr
    #
    w3a
    #
    wn
    @3
    cmnf
    cc0
    clt
    wbr
    #
    @5
    mnflt0
    @6
    cc0
    cxr
    wcel
    #
    @9
    @5
    wb
    mnfxr
    0xr
    cmnf
    cc0
    xrltnle
    mp2an
    mpbi
    @8
    @4
    @6
    @4
    @7
    simp2
    con3i
    @2
    @8
    @2
    @8
    @10
    cpnf
    cxr
    wcel
    @2
    @8
    wb
    0xr
    pnfxr
    cc0
    cpnf
    cmnf
    elicc1
    mp2an
    biimpi
    con3i
    mp2b
    cA
    cmnf
    @0
    nelneq
    mpan2
    neqned
end
