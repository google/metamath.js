include "cc0.mm"
include "c1.mm"
include "cico.mm"
include "co.mm"
include "wcel.mm"
include "cr.mm"
include "cle.mm"
include "wbr.mm"
include "clt.mm"
include "cfl.mm"
include "cfv.mm"
include "wceq.mm"
include "cxr.mm"
include "wss.mm"
include "0re.mm"
include "1re.mm"
include "rexri.mm"
include "icossre.mm"
include "mp2an.mm"
include "sseli.mm"
include "w3a.mm"
include "wb.mm"
include "0xr.mm"
include "elico1.mm"
include "simp2bi.mm"
include "simp3bi.mm"
include "wa.mm"
include "caddc.mm"
include "recn.mm"
include "addid2d.mm"
include "fveq2d.mm"
include "eqeq1d.mm"
include "cz.mm"
include "0z.mm"
include "flbi2.mm"
include "mpan.mm"
include "bitr3d.mm"
include "biimpar.mm"
include "syl12anc.mm"

theorem ico01fl0
  let cA: class A


  assert |- ( A e. ( 0 [,) 1 ) -> ( |_ ` A ) = 0 )

  proof
    cA
    cc0
    c1
    cico
    co
    #
    wcel
    #
    cA
    cr
    wcel
    #
    cc0
    cA
    cle
    wbr
    #
    cA
    c1
    clt
    wbr
    #
    cA
    cfl
    cfv
    #
    cc0
    wceq
    #
    @0
    cr
    cA
    cc0
    cr
    wcel
    c1
    cxr
    wcel
    #
    @0
    cr
    wss
    0re
    c1
    1re
    rexri
    #
    cc0
    c1
    icossre
    mp2an
    sseli
    @1
    cA
    cxr
    wcel
    #
    @3
    @4
    cc0
    cxr
    wcel
    @7
    @1
    @9
    @3
    @4
    w3a
    wb
    0xr
    @8
    cc0
    c1
    cA
    elico1
    mp2an
    #
    simp2bi
    @1
    @9
    @3
    @4
    @10
    simp3bi
    @2
    @6
    @3
    @4
    wa
    #
    @2
    cc0
    cA
    caddc
    co
    #
    cfl
    cfv
    #
    cc0
    wceq
    #
    @6
    @11
    @2
    @13
    @5
    cc0
    @2
    @12
    cA
    cfl
    @2
    cA
    cA
    recn
    addid2d
    fveq2d
    eqeq1d
    cc0
    cz
    wcel
    @2
    @14
    @11
    wb
    0z
    cA
    cc0
    flbi2
    mpan
    bitr3d
    biimpar
    syl12anc
end
