include "wcel.mm"
include "cpw.mm"
include "com.mm"
include "cdom.mm"
include "wbr.mm"
include "cdif.mm"
include "wo.mm"
include "wa.mm"
include "wn.mm"
include "wtru.mm"
include "cc0.mm"
include "c1.mm"
include "cxr.mm"
include "0xr.mm"
include "a1i.mm"
include "1re.mm"
include "rexri.mm"
include "clt.mm"
include "0lt1.mm"
include "iccnct.mm"
include "trud.mm"
include "c2.mm"
include "cioc.mm"
include "co.mm"
include "2re.mm"
include "1lt2.mm"
include "eqid.mm"
include "iocnct.mm"
include "cicc.mm"
include "difeq12i.mm"
include "wceq.mm"
include "xrltled.mm"
include "iccdificc.mm"
include "eqtri.mm"
include "breq1i.mm"
include "mtbir.mm"
include "pm3.2i.mm"
include "ioran.mm"
include "mpbir.mm"
include "intnan.mm"
include "cv.mm"
include "breq1.mm"
include "difeq2.mm"
include "breq1d.mm"
include "orbi12d.mm"
include "elrab2.mm"

theorem salexct2
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cS: class S
  let vk: setvar k
  assume salexct2.1: |- A = ( 0 [,] 2 )
  assume salexct2.2: |- S = { x e. ~P A | ( x ~<_ _om \/ ( A \ x ) ~<_ _om ) }
  assume salexct2.3: |- B = ( 0 [,] 1 )

  disjoint A x
  disjoint B x
  disjoint k x
  assert |- -. B e. S

  proof
    cB
    cS
    wcel
    cB
    cA
    cpw
    #
    wcel
    #
    cB
    com
    cdom
    wbr
    #
    cA
    cB
    cdif
    #
    com
    cdom
    wbr
    #
    wo
    #
    wa
    @5
    @1
    @5
    wn
    @2
    wn
    #
    @4
    wn
    #
    wa
    @6
    @7
    @6
    wtru
    cc0
    c1
    cB
    cc0
    cxr
    wcel
    wtru
    0xr
    a1i
    #
    c1
    cxr
    wcel
    wtru
    c1
    1re
    rexri
    a1i
    #
    cc0
    c1
    clt
    wbr
    wtru
    0lt1
    a1i
    #
    salexct2.3
    iccnct
    trud
    @4
    c1
    c2
    cioc
    co
    #
    com
    cdom
    wbr
    #
    @12
    wn
    wtru
    c1
    c2
    @11
    @9
    c2
    cxr
    wcel
    wtru
    c2
    2re
    rexri
    a1i
    #
    c1
    c2
    clt
    wbr
    wtru
    1lt2
    a1i
    @11
    eqid
    iocnct
    trud
    @3
    @11
    com
    cdom
    @3
    cc0
    c2
    cicc
    co
    #
    cc0
    c1
    cicc
    co
    #
    cdif
    #
    @11
    cA
    @14
    cB
    @15
    salexct2.1
    salexct2.3
    difeq12i
    @16
    @11
    wceq
    wtru
    cc0
    c1
    c2
    @8
    @9
    @13
    wtru
    cc0
    c1
    @8
    @9
    @10
    xrltled
    iccdificc
    trud
    eqtri
    breq1i
    mtbir
    pm3.2i
    @2
    @4
    ioran
    mpbir
    intnan
    vx
    cv
    #
    com
    cdom
    wbr
    #
    cA
    @17
    cdif
    #
    com
    cdom
    wbr
    #
    wo
    @5
    vx
    cB
    @0
    cS
    @17
    cB
    wceq
    #
    @18
    @2
    @20
    @4
    @17
    cB
    com
    cdom
    breq1
    @21
    @19
    @3
    com
    cdom
    @17
    cB
    cA
    difeq2
    breq1d
    orbi12d
    salexct2.2
    elrab2
    mtbir
end
