include "wcel.mm"
include "cpo.mm"
include "cjn.mm"
include "cfv.mm"
include "cdm.mm"
include "cbs.mm"
include "cxp.mm"
include "wceq.mm"
include "cmee.mm"
include "wa.mm"
include "clat.mm"
include "oduposb.mm"
include "wb.mm"
include "ancom.mm"
include "a1i.mm"
include "anbi12d.mm"
include "eqid.mm"
include "islat.mm"
include "odubas.mm"
include "odujoin.mm"
include "odumeet.mm"
include "3bitr4g.mm"

theorem odulatb
  let cD: class D
  let cO: class O
  let cV: class V
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d
  let cL: class L
  let cU: class U
  let c.or: class .\/
  let c.an: class ./\
  assume oduglb.d: |- D = ( ODual ` O )


  assert |- ( O e. V -> ( O e. Lat <-> D e. Lat ) )

  proof
    cO
    cV
    wcel
    #
    cO
    cpo
    wcel
    #
    cO
    cjn
    cfv
    #
    cdm
    cO
    cbs
    cfv
    #
    @3
    cxp
    #
    wceq
    #
    cO
    cmee
    cfv
    #
    cdm
    @4
    wceq
    #
    wa
    #
    wa
    cD
    cpo
    wcel
    #
    @7
    @5
    wa
    #
    wa
    cO
    clat
    wcel
    cD
    clat
    wcel
    @0
    @1
    @9
    @8
    @10
    cD
    cO
    cV
    oduglb.d
    oduposb
    @8
    @10
    wb
    @0
    @5
    @7
    ancom
    a1i
    anbi12d
    @3
    @2
    cO
    @6
    @3
    eqid
    #
    @2
    eqid
    #
    @6
    eqid
    #
    islat
    @3
    @6
    cD
    @2
    @3
    cD
    cO
    oduglb.d
    @11
    odubas
    cD
    @6
    cO
    oduglb.d
    @13
    odujoin
    cD
    @2
    cO
    oduglb.d
    @12
    odumeet
    islat
    3bitr4g
end
