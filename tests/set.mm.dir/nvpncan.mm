include "cnv.mm"
include "wcel.mm"
include "co.mm"
include "wceq.mm"
include "w3a.mm"
include "nvcom.mm"
include "oveq1d.mm"
include "nvpncan2.mm"
include "eqtr3d.mm"
include "3com23.mm"

theorem nvpncan
  let cA: class A
  let cB: class B
  let cU: class U
  let cG: class G
  let cM: class M
  let cX: class X
  assume nvpncan2.1: |- X = ( BaseSet ` U )
  assume nvpncan2.2: |- G = ( +v ` U )
  assume nvpncan2.3: |- M = ( -v ` U )


  assert |- ( ( U e. NrmCVec /\ A e. X /\ B e. X ) -> ( ( A G B ) M B ) = A )

  proof
    cU
    cnv
    wcel
    #
    cB
    cX
    wcel
    #
    cA
    cX
    wcel
    #
    cA
    cB
    cG
    co
    #
    cB
    cM
    co
    #
    cA
    wceq
    @0
    @1
    @2
    w3a
    #
    cB
    cA
    cG
    co
    #
    cB
    cM
    co
    @4
    cA
    @5
    @6
    @3
    cB
    cM
    cB
    cA
    cU
    cG
    cX
    nvpncan2.1
    nvpncan2.2
    nvcom
    oveq1d
    cB
    cA
    cU
    cG
    cM
    cX
    nvpncan2.1
    nvpncan2.2
    nvpncan2.3
    nvpncan2
    eqtr3d
    3com23
end
