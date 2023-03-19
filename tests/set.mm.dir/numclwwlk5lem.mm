include "c2.mm"
include "cclwwlknon.mm"
include "cfv.mm"
include "co.mm"
include "chash.mm"
include "wceq.mm"
include "crusgr.mm"
include "wbr.mm"
include "wcel.mm"
include "cn0.mm"
include "w3a.mm"
include "c1.mm"
include "cmin.mm"
include "cdvds.mm"
include "cmo.mm"
include "wi.mm"
include "cvtx.mm"
include "eleq2i.mm"
include "clwwlknon2num.mm"
include "sylan2b.mm"
include "3adant3.mm"
include "wa.mm"
include "oveq1.mm"
include "ad2antrr.mm"
include "cprime.mm"
include "cz.mm"
include "wb.mm"
include "2prm.mm"
include "nn0z.mm"
include "modprm1div.mm"
include "sylancr.mm"
include "biimprd.mm"
include "3ad2ant3.mm"
include "adantl.mm"
include "imp.mm"
include "eqtrd.mm"
include "ex.mm"
include "mpancom.mm"

theorem numclwwlk5lem
  let cG: class G
  let cK: class K
  let cV: class V
  let cX: class X
  let vn: setvar n
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
  let cN: class N
  let vx: setvar x
  assume numclwwlk3.v: |- V = ( Vtx ` G )


  assert |- ( ( G RegUSGraph K /\ X e. V /\ K e. NN0 ) -> ( 2 || ( K - 1 ) -> ( ( # ` ( X ( ClWWalksNOn ` G ) 2 ) ) mod 2 ) = 1 ) )

  proof
    cX
    c2
    cG
    cclwwlknon
    cfv
    co
    chash
    cfv
    #
    cK
    wceq
    #
    cG
    cK
    crusgr
    wbr
    #
    cX
    cV
    wcel
    #
    cK
    cn0
    wcel
    #
    w3a
    #
    c2
    cK
    c1
    cmin
    co
    cdvds
    wbr
    #
    @0
    c2
    cmo
    co
    #
    c1
    wceq
    #
    wi
    @2
    @3
    @1
    @4
    @3
    @2
    cX
    cG
    cvtx
    cfv
    #
    wcel
    @1
    cV
    @9
    cX
    numclwwlk3.v
    eleq2i
    cG
    cK
    cX
    clwwlknon2num
    sylan2b
    3adant3
    @1
    @5
    wa
    #
    @6
    @8
    @10
    @6
    wa
    @7
    cK
    c2
    cmo
    co
    #
    c1
    @1
    @7
    @11
    wceq
    @5
    @6
    @0
    cK
    c2
    cmo
    oveq1
    ad2antrr
    @10
    @6
    @11
    c1
    wceq
    #
    @5
    @6
    @12
    wi
    #
    @1
    @4
    @2
    @13
    @3
    @4
    @12
    @6
    @4
    c2
    cprime
    wcel
    cK
    cz
    wcel
    @12
    @6
    wb
    2prm
    cK
    nn0z
    cK
    c2
    modprm1div
    sylancr
    biimprd
    3ad2ant3
    adantl
    imp
    eqtrd
    ex
    mpancom
end
