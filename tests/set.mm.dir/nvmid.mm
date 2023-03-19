include "cnv.mm"
include "wcel.mm"
include "wa.mm"
include "co.mm"
include "wceq.mm"
include "eqid.mm"
include "wb.mm"
include "nvmeq0.mm"
include "3anidm23.mm"
include "mpbiri.mm"

theorem nvmid
  let cA: class A
  let cU: class U
  let cM: class M
  let cX: class X
  let cZ: class Z
  assume nvmeq0.1: |- X = ( BaseSet ` U )
  assume nvmeq0.3: |- M = ( -v ` U )
  assume nvmeq0.5: |- Z = ( 0vec ` U )


  assert |- ( ( U e. NrmCVec /\ A e. X ) -> ( A M A ) = Z )

  proof
    cU
    cnv
    wcel
    #
    cA
    cX
    wcel
    #
    wa
    cA
    cA
    cM
    co
    cZ
    wceq
    #
    cA
    cA
    wceq
    #
    cA
    eqid
    @0
    @1
    @2
    @3
    wb
    cA
    cA
    cU
    cM
    cX
    cZ
    nvmeq0.1
    nvmeq0.3
    nvmeq0.5
    nvmeq0
    3anidm23
    mpbiri
end
