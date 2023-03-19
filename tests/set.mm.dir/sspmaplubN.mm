include "chlt.mm"
include "wcel.mm"
include "wss.mm"
include "wa.mm"
include "cpolN.mm"
include "cfv.mm"
include "eqid.mm"
include "2polssN.mm"
include "2polvalN.mm"
include "sseqtrd.mm"

theorem sspmaplubN
  let cA: class A
  let cS: class S
  let cU: class U
  let cK: class K
  let cM: class M
  assume sspmaplub.u: |- U = ( lub ` K )
  assume sspmaplub.a: |- A = ( Atoms ` K )
  assume sspmaplub.m: |- M = ( pmap ` K )


  assert |- ( ( K e. HL /\ S C_ A ) -> S C_ ( M ` ( U ` S ) ) )

  proof
    cK
    chlt
    wcel
    cS
    cA
    wss
    wa
    cS
    cS
    cK
    cpolN
    cfv
    #
    cfv
    @0
    cfv
    cS
    cU
    cfv
    cM
    cfv
    cA
    cK
    @0
    cS
    sspmaplub.a
    @0
    eqid
    #
    2polssN
    cA
    cU
    cK
    cM
    @0
    cS
    sspmaplub.u
    sspmaplub.a
    sspmaplub.m
    @1
    2polvalN
    sseqtrd
end
