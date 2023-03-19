include "wcel.mm"
include "co.mm"
include "cabs.mm"
include "cfv.mm"
include "cmul.mm"
include "cle.mm"
include "wbr.mm"
include "cn0v.mm"
include "cif.mm"
include "wceq.mm"
include "oveq1.mm"
include "fveq2d.mm"
include "fveq2.mm"
include "oveq1d.mm"
include "breq12d.mm"
include "oveq2.mm"
include "oveq2d.mm"
include "eqid.mm"
include "elimph.mm"
include "siii.mm"
include "dedth2h.mm"

theorem sii
  let cA: class A
  let cB: class B
  let cP: class P
  let cU: class U
  let cN: class N
  let cX: class X
  assume sii.1: |- X = ( BaseSet ` U )
  assume sii.6: |- N = ( normCV ` U )
  assume sii.7: |- P = ( .iOLD ` U )
  assume sii.9: |- U e. CPreHilOLD


  assert |- ( ( A e. X /\ B e. X ) -> ( abs ` ( A P B ) ) <_ ( ( N ` A ) x. ( N ` B ) ) )

  proof
    cA
    cX
    wcel
    #
    cB
    cX
    wcel
    #
    cA
    cB
    cP
    co
    #
    cabs
    cfv
    #
    cA
    cN
    cfv
    #
    cB
    cN
    cfv
    #
    cmul
    co
    #
    cle
    wbr
    @0
    cA
    cU
    cn0v
    cfv
    #
    cif
    #
    cB
    cP
    co
    #
    cabs
    cfv
    #
    @8
    cN
    cfv
    #
    @5
    cmul
    co
    #
    cle
    wbr
    @8
    @1
    cB
    @7
    cif
    #
    cP
    co
    #
    cabs
    cfv
    #
    @11
    @13
    cN
    cfv
    #
    cmul
    co
    #
    cle
    wbr
    cA
    cB
    @7
    @7
    cA
    @8
    wceq
    #
    @3
    @10
    @6
    @12
    cle
    @18
    @2
    @9
    cabs
    cA
    @8
    cB
    cP
    oveq1
    fveq2d
    @18
    @4
    @11
    @5
    cmul
    cA
    @8
    cN
    fveq2
    oveq1d
    breq12d
    cB
    @13
    wceq
    #
    @10
    @15
    @12
    @17
    cle
    @19
    @9
    @14
    cabs
    cB
    @13
    @8
    cP
    oveq2
    fveq2d
    @19
    @5
    @16
    @11
    cmul
    cB
    @13
    cN
    fveq2
    oveq2d
    breq12d
    @8
    @13
    cP
    cU
    cN
    cX
    sii.1
    sii.6
    sii.7
    sii.9
    cA
    cU
    cX
    @7
    sii.1
    @7
    eqid
    #
    sii.9
    elimph
    cB
    cU
    cX
    @7
    sii.1
    @20
    sii.9
    elimph
    siii
    dedth2h
end
