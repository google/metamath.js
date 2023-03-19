include "cnv.mm"
include "wcel.mm"
include "w3a.mm"
include "cc.mm"
include "wa.mm"
include "co.mm"
include "cfv.mm"
include "cr.mm"
include "simpl1.mm"
include "simpl2.mm"
include "nvscl.mm"
include "3com23.mm"
include "3expa.mm"
include "3adantl2.mm"
include "nvgcl.mm"
include "syl3anc.mm"
include "nvcl.mm"
include "syl2anc.mm"
include "resqcld.mm"

theorem ipval2lem2
  let cA: class A
  let cB: class B
  let cC: class C
  let cP: class P
  let cS: class S
  let cU: class U
  let cG: class G
  let cN: class N
  let cX: class X
  let vk: setvar k
  let vu: setvar u
  let vx: setvar x
  let vy: setvar y
  assume dipfval.1: |- X = ( BaseSet ` U )
  assume dipfval.2: |- G = ( +v ` U )
  assume dipfval.4: |- S = ( .sOLD ` U )
  assume dipfval.6: |- N = ( normCV ` U )
  assume dipfval.7: |- P = ( .iOLD ` U )


  assert |- ( ( ( U e. NrmCVec /\ A e. X /\ B e. X ) /\ C e. CC ) -> ( ( N ` ( A G ( C S B ) ) ) ^ 2 ) e. RR )

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
    cC
    cc
    wcel
    #
    wa
    #
    cA
    cC
    cB
    cS
    co
    #
    cG
    co
    #
    cN
    cfv
    #
    @4
    @0
    @6
    cX
    wcel
    #
    @7
    cr
    wcel
    @0
    @1
    @2
    @3
    simpl1
    #
    @4
    @0
    @1
    @5
    cX
    wcel
    #
    @8
    @9
    @0
    @1
    @2
    @3
    simpl2
    @0
    @2
    @3
    @10
    @1
    @0
    @2
    @3
    @10
    @0
    @3
    @2
    @10
    cC
    cB
    cS
    cU
    cX
    dipfval.1
    dipfval.4
    nvscl
    3com23
    3expa
    3adantl2
    cA
    @5
    cU
    cG
    cX
    dipfval.1
    dipfval.2
    nvgcl
    syl3anc
    @6
    cU
    cN
    cX
    dipfval.1
    dipfval.6
    nvcl
    syl2anc
    resqcld
end
