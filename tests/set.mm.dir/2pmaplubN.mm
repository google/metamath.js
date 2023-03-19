include "chlt.mm"
include "wcel.mm"
include "wss.mm"
include "wa.mm"
include "cpolN.mm"
include "cfv.mm"
include "eqid.mm"
include "2polvalN.mm"
include "fveq2d.mm"
include "wceq.mm"
include "polssatN.mm"
include "3polN.mm"
include "syldan.mm"
include "eqtr3d.mm"
include "cbs.mm"
include "ccla.mm"
include "hlclat.mm"
include "atssbase.mm"
include "sstr.mm"
include "mpan2.mm"
include "clatlubcl.mm"
include "syl2an.mm"
include "pmapssat.mm"

theorem 2pmaplubN
  let cA: class A
  let cS: class S
  let cU: class U
  let cK: class K
  let cM: class M
  assume sspmaplub.u: |- U = ( lub ` K )
  assume sspmaplub.a: |- A = ( Atoms ` K )
  assume sspmaplub.m: |- M = ( pmap ` K )


  assert |- ( ( K e. HL /\ S C_ A ) -> ( M ` ( U ` ( M ` ( U ` S ) ) ) ) = ( M ` ( U ` S ) ) )

  proof
    cK
    chlt
    wcel
    #
    cS
    cA
    wss
    #
    wa
    #
    cS
    cK
    cpolN
    cfv
    #
    cfv
    #
    @3
    cfv
    #
    cS
    cU
    cfv
    #
    cM
    cfv
    #
    cU
    cfv
    cM
    cfv
    #
    @7
    @2
    @7
    @3
    cfv
    #
    @3
    cfv
    #
    @5
    @8
    @2
    @5
    @3
    cfv
    #
    @3
    cfv
    #
    @10
    @5
    @2
    @11
    @9
    @3
    @2
    @5
    @7
    @3
    cA
    cU
    cK
    cM
    @3
    cS
    sspmaplub.u
    sspmaplub.a
    sspmaplub.m
    @3
    eqid
    #
    2polvalN
    #
    fveq2d
    fveq2d
    @0
    @1
    @4
    cA
    wss
    @12
    @5
    wceq
    cA
    cK
    @3
    cS
    sspmaplub.a
    @13
    polssatN
    cA
    @4
    cK
    @3
    sspmaplub.a
    @13
    3polN
    syldan
    eqtr3d
    @0
    @1
    @7
    cA
    wss
    #
    @10
    @8
    wceq
    @0
    @1
    @6
    cK
    cbs
    cfv
    #
    wcel
    #
    @15
    @0
    cK
    ccla
    wcel
    cS
    @16
    wss
    #
    @17
    @1
    cK
    hlclat
    @1
    cA
    @16
    wss
    @18
    cA
    @16
    cK
    @16
    eqid
    #
    sspmaplub.a
    atssbase
    cS
    cA
    @16
    sstr
    mpan2
    @16
    cS
    cU
    cK
    @19
    sspmaplub.u
    clatlubcl
    syl2an
    cA
    @16
    chlt
    cK
    cM
    @6
    @19
    sspmaplub.a
    sspmaplub.m
    pmapssat
    syldan
    cA
    cU
    cK
    cM
    @3
    @7
    sspmaplub.u
    sspmaplub.a
    sspmaplub.m
    @13
    2polvalN
    syldan
    eqtr3d
    @14
    eqtr3d
end
