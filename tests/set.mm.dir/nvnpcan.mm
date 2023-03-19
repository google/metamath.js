include "cnv.mm"
include "wcel.mm"
include "w3a.mm"
include "co.mm"
include "wceq.mm"
include "wa.mm"
include "simprl.mm"
include "simprr.mm"
include "3jca.mm"
include "nvaddsub.mm"
include "syldan.mm"
include "3impb.mm"
include "nvpncan.mm"
include "eqtr3d.mm"

theorem nvnpcan
  let cA: class A
  let cB: class B
  let cU: class U
  let cG: class G
  let cM: class M
  let cX: class X
  assume nvpncan2.1: |- X = ( BaseSet ` U )
  assume nvpncan2.2: |- G = ( +v ` U )
  assume nvpncan2.3: |- M = ( -v ` U )


  assert |- ( ( U e. NrmCVec /\ A e. X /\ B e. X ) -> ( ( A M B ) G B ) = A )

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
    cA
    cB
    cG
    co
    cB
    cM
    co
    #
    cA
    cB
    cM
    co
    cB
    cG
    co
    #
    cA
    @0
    @1
    @2
    @3
    @4
    wceq
    #
    @0
    @1
    @2
    wa
    #
    @1
    @2
    @2
    w3a
    @5
    @0
    @6
    wa
    @1
    @2
    @2
    @0
    @1
    @2
    simprl
    @0
    @1
    @2
    simprr
    #
    @7
    3jca
    cA
    cB
    cB
    cU
    cG
    cM
    cX
    nvpncan2.1
    nvpncan2.2
    nvpncan2.3
    nvaddsub
    syldan
    3impb
    cA
    cB
    cU
    cG
    cM
    cX
    nvpncan2.1
    nvpncan2.2
    nvpncan2.3
    nvpncan
    eqtr3d
end
