include "cnv.mm"
include "wcel.mm"
include "w3a.mm"
include "co.mm"
include "cpv.mm"
include "cfv.mm"
include "wceq.mm"
include "wb.mm"
include "wa.mm"
include "nvmcl.mm"
include "3expb.mm"
include "nvzcl.mm"
include "adantr.mm"
include "simprr.mm"
include "3jca.mm"
include "eqid.mm"
include "nvrcan.mm"
include "syldan.mm"
include "3impb.mm"
include "nvnpcan.mm"
include "nv0lid.mm"
include "3adant2.mm"
include "eqeq12d.mm"
include "bitr3d.mm"

theorem nvmeq0
  let cA: class A
  let cB: class B
  let cU: class U
  let cM: class M
  let cX: class X
  let cZ: class Z
  assume nvmeq0.1: |- X = ( BaseSet ` U )
  assume nvmeq0.3: |- M = ( -v ` U )
  assume nvmeq0.5: |- Z = ( 0vec ` U )


  assert |- ( ( U e. NrmCVec /\ A e. X /\ B e. X ) -> ( ( A M B ) = Z <-> A = B ) )

  proof
    cU
    cnv
    wcel
    #
    cA
    cX
    wcel
    #
    cB
    cX
    wcel
    #
    w3a
    #
    cA
    cB
    cM
    co
    #
    cB
    cU
    cpv
    cfv
    #
    co
    #
    cZ
    cB
    @5
    co
    #
    wceq
    #
    @4
    cZ
    wceq
    #
    cA
    cB
    wceq
    @0
    @1
    @2
    @8
    @9
    wb
    #
    @0
    @1
    @2
    wa
    #
    @4
    cX
    wcel
    #
    cZ
    cX
    wcel
    #
    @2
    w3a
    @10
    @0
    @11
    wa
    @12
    @13
    @2
    @0
    @1
    @2
    @12
    cA
    cB
    cU
    cM
    cX
    nvmeq0.1
    nvmeq0.3
    nvmcl
    3expb
    @0
    @13
    @11
    cU
    cX
    cZ
    nvmeq0.1
    nvmeq0.5
    nvzcl
    adantr
    @0
    @1
    @2
    simprr
    3jca
    @4
    cZ
    cB
    cU
    @5
    cX
    nvmeq0.1
    @5
    eqid
    #
    nvrcan
    syldan
    3impb
    @3
    @6
    cA
    @7
    cB
    cA
    cB
    cU
    @5
    cM
    cX
    nvmeq0.1
    @14
    nvmeq0.3
    nvnpcan
    @0
    @2
    @7
    cB
    wceq
    @1
    cB
    cU
    @5
    cX
    cZ
    nvmeq0.1
    @14
    nvmeq0.5
    nv0lid
    3adant2
    eqeq12d
    bitr3d
end
