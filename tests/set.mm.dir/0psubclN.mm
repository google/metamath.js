include "chlt.mm"
include "wcel.mm"
include "c0.mm"
include "catm.mm"
include "cfv.mm"
include "wss.mm"
include "cpolN.mm"
include "wceq.mm"
include "0ss.mm"
include "a1i.mm"
include "eqid.mm"
include "2pol0N.mm"
include "ispsubclN.mm"
include "mpbir2and.mm"

theorem 0psubclN
  let cC: class C
  let cK: class K
  assume 0psubcl.c: |- C = ( PSubCl ` K )


  assert |- ( K e. HL -> (/) e. C )

  proof
    cK
    chlt
    wcel
    #
    c0
    cC
    wcel
    c0
    cK
    catm
    cfv
    #
    wss
    #
    c0
    cK
    cpolN
    cfv
    #
    cfv
    @3
    cfv
    c0
    wceq
    @2
    @0
    @1
    0ss
    a1i
    cK
    @3
    @3
    eqid
    #
    2pol0N
    @1
    cC
    chlt
    cK
    @3
    c0
    @1
    eqid
    @4
    0psubcl.c
    ispsubclN
    mpbir2and
end
