include "chlt.mm"
include "wcel.mm"
include "wss.mm"
include "cpolN.mm"
include "cfv.mm"
include "wceq.mm"
include "ssid.mm"
include "a1i.mm"
include "c0.mm"
include "eqid.mm"
include "pol1N.mm"
include "fveq2d.mm"
include "pol0N.mm"
include "eqtrd.mm"
include "ispsubclN.mm"
include "mpbir2and.mm"

theorem 1psubclN
  let cA: class A
  let cC: class C
  let cK: class K
  assume 1psubcl.a: |- A = ( Atoms ` K )
  assume 1psubcl.c: |- C = ( PSubCl ` K )


  assert |- ( K e. HL -> A e. C )

  proof
    cK
    chlt
    wcel
    #
    cA
    cC
    wcel
    cA
    cA
    wss
    #
    cA
    cK
    cpolN
    cfv
    #
    cfv
    #
    @2
    cfv
    #
    cA
    wceq
    @1
    @0
    cA
    ssid
    a1i
    @0
    @4
    c0
    @2
    cfv
    cA
    @0
    @3
    c0
    @2
    cA
    cK
    @2
    1psubcl.a
    @2
    eqid
    #
    pol1N
    fveq2d
    cA
    chlt
    cK
    @2
    1psubcl.a
    @5
    pol0N
    eqtrd
    cA
    cC
    chlt
    cK
    @2
    cA
    1psubcl.a
    @5
    1psubcl.c
    ispsubclN
    mpbir2and
end
