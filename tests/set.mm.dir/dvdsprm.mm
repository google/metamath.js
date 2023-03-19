include "c2.mm"
include "cuz.mm"
include "cfv.mm"
include "wcel.mm"
include "cprime.mm"
include "wa.mm"
include "cdvds.mm"
include "wbr.mm"
include "wceq.mm"
include "wi.mm"
include "cv.mm"
include "wral.mm"
include "isprm4.mm"
include "simprbi.mm"
include "breq1.mm"
include "eqeq1.mm"
include "imbi12d.mm"
include "rspcv.mm"
include "mpan9.mm"
include "ancoms.mm"
include "cz.mm"
include "eluzelz.mm"
include "iddvds.mm"
include "breq2.mm"
include "syl5ibcom.mm"
include "syl.mm"
include "adantr.mm"
include "impbid.mm"

theorem dvdsprm
  let cP: class P
  let cN: class N
  let vz: setvar z


  assert |- ( ( N e. ( ZZ>= ` 2 ) /\ P e. Prime ) -> ( N || P <-> N = P ) )

  proof
    cN
    c2
    cuz
    cfv
    #
    wcel
    #
    cP
    cprime
    wcel
    #
    wa
    cN
    cP
    cdvds
    wbr
    #
    cN
    cP
    wceq
    #
    @2
    @1
    @3
    @4
    wi
    #
    @2
    vz
    cv
    #
    cP
    cdvds
    wbr
    #
    @6
    cP
    wceq
    #
    wi
    #
    vz
    @0
    wral
    #
    @1
    @5
    @2
    cP
    @0
    wcel
    @10
    vz
    cP
    isprm4
    simprbi
    @9
    @5
    vz
    cN
    @0
    @6
    cN
    wceq
    @7
    @3
    @8
    @4
    @6
    cN
    cP
    cdvds
    breq1
    @6
    cN
    cP
    eqeq1
    imbi12d
    rspcv
    mpan9
    ancoms
    @1
    @4
    @3
    wi
    #
    @2
    @1
    cN
    cz
    wcel
    #
    @11
    c2
    cN
    eluzelz
    @12
    cN
    cN
    cdvds
    wbr
    @4
    @3
    cN
    iddvds
    cN
    cP
    cN
    cdvds
    breq2
    syl5ibcom
    syl
    adantr
    impbid
end
