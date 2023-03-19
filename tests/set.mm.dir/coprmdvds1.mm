include "cn.mm"
include "wcel.mm"
include "cgcd.mm"
include "co.mm"
include "c1.mm"
include "wceq.mm"
include "cdvds.mm"
include "wbr.mm"
include "w3a.mm"
include "wi.mm"
include "wa.mm"
include "cv.mm"
include "wral.mm"
include "coprmgcdb.mm"
include "breq1.mm"
include "anbi12d.mm"
include "eqeq1.mm"
include "imbi12d.mm"
include "rspcv.mm"
include "com23.mm"
include "3impib.mm"
include "com12.mm"
include "syl6bir.mm"
include "3impia.mm"

theorem coprmdvds1
  let cF: class F
  let cG: class G
  let cI: class I
  let vi: setvar i


  assert |- ( ( F e. NN /\ G e. NN /\ ( F gcd G ) = 1 ) -> ( ( I e. NN /\ I || F /\ I || G ) -> I = 1 ) )

  proof
    cF
    cn
    wcel
    #
    cG
    cn
    wcel
    #
    cF
    cG
    cgcd
    co
    c1
    wceq
    #
    cI
    cn
    wcel
    #
    cI
    cF
    cdvds
    wbr
    #
    cI
    cG
    cdvds
    wbr
    #
    w3a
    #
    cI
    c1
    wceq
    #
    wi
    #
    @0
    @1
    wa
    @2
    vi
    cv
    #
    cF
    cdvds
    wbr
    #
    @9
    cG
    cdvds
    wbr
    #
    wa
    #
    @9
    c1
    wceq
    #
    wi
    #
    vi
    cn
    wral
    #
    @8
    cF
    cG
    vi
    coprmgcdb
    @6
    @15
    @7
    @3
    @4
    @5
    @15
    @7
    wi
    @3
    @15
    @4
    @5
    wa
    #
    @7
    @14
    @16
    @7
    wi
    vi
    cI
    cn
    @9
    cI
    wceq
    #
    @12
    @16
    @13
    @7
    @17
    @10
    @4
    @11
    @5
    @9
    cI
    cF
    cdvds
    breq1
    @9
    cI
    cG
    cdvds
    breq1
    anbi12d
    @9
    cI
    c1
    eqeq1
    imbi12d
    rspcv
    com23
    3impib
    com12
    syl6bir
    3impia
end
