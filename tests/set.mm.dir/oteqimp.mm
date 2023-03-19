include "wcel.mm"
include "w3a.mm"
include "c1st.mm"
include "cfv.mm"
include "wceq.mm"
include "c2nd.mm"
include "cotp.mm"
include "ot1stg.mm"
include "ot2ndg.mm"
include "ot3rdg.mm"
include "3ad2ant3.mm"
include "3jca.mm"
include "fveq2.mm"
include "fveq2d.mm"
include "eqeq1d.mm"
include "3anbi123d.mm"
include "syl5ibr.mm"

theorem oteqimp
  let cA: class A
  let cB: class B
  let cC: class C
  let cT: class T
  let cX: class X
  let cY: class Y
  let cZ: class Z


  assert |- ( T = <. A , B , C >. -> ( ( A e. X /\ B e. Y /\ C e. Z ) -> ( ( 1st ` ( 1st ` T ) ) = A /\ ( 2nd ` ( 1st ` T ) ) = B /\ ( 2nd ` T ) = C ) ) )

  proof
    cA
    cX
    wcel
    #
    cB
    cY
    wcel
    #
    cC
    cZ
    wcel
    #
    w3a
    #
    cT
    c1st
    cfv
    #
    c1st
    cfv
    #
    cA
    wceq
    #
    @4
    c2nd
    cfv
    #
    cB
    wceq
    #
    cT
    c2nd
    cfv
    #
    cC
    wceq
    #
    w3a
    cT
    cA
    cB
    cC
    cotp
    #
    wceq
    #
    @11
    c1st
    cfv
    #
    c1st
    cfv
    #
    cA
    wceq
    #
    @13
    c2nd
    cfv
    #
    cB
    wceq
    #
    @11
    c2nd
    cfv
    #
    cC
    wceq
    #
    w3a
    @3
    @15
    @17
    @19
    cA
    cB
    cC
    cX
    cY
    cZ
    ot1stg
    cA
    cB
    cC
    cX
    cY
    cZ
    ot2ndg
    @2
    @0
    @19
    @1
    cA
    cB
    cC
    cZ
    ot3rdg
    3ad2ant3
    3jca
    @12
    @6
    @15
    @8
    @17
    @10
    @19
    @12
    @5
    @14
    cA
    @12
    @4
    @13
    c1st
    cT
    @11
    c1st
    fveq2
    #
    fveq2d
    eqeq1d
    @12
    @7
    @16
    cB
    @12
    @4
    @13
    c2nd
    @20
    fveq2d
    eqeq1d
    @12
    @9
    @18
    cC
    cT
    @11
    c2nd
    fveq2
    eqeq1d
    3anbi123d
    syl5ibr
end
