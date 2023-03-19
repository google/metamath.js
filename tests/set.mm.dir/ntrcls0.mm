include "ctop.mm"
include "wcel.mm"
include "wss.mm"
include "ccl.mm"
include "cfv.mm"
include "cnt.mm"
include "c0.mm"
include "wceq.mm"
include "w3a.mm"
include "wa.mm"
include "simpl.mm"
include "clsss3.mm"
include "sscls.mm"
include "ntrss.mm"
include "syl3anc.mm"
include "3adant3.mm"
include "wb.mm"
include "sseq2.mm"
include "3ad2ant3.mm"
include "mpbid.mm"
include "ss0.mm"
include "syl.mm"

theorem ntrcls0
  let cS: class S
  let cJ: class J
  let cX: class X
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cP: class P
  let cU: class U
  let cT: class T
  let cA: class A
  assume clscld.1: |- X = U. J


  assert |- ( ( J e. Top /\ S C_ X /\ ( ( int ` J ) ` ( ( cls ` J ) ` S ) ) = (/) ) -> ( ( int ` J ) ` S ) = (/) )

  proof
    cJ
    ctop
    wcel
    #
    cS
    cX
    wss
    #
    cS
    cJ
    ccl
    cfv
    cfv
    #
    cJ
    cnt
    cfv
    #
    cfv
    #
    c0
    wceq
    #
    w3a
    #
    cS
    @3
    cfv
    #
    c0
    wss
    #
    @7
    c0
    wceq
    @6
    @7
    @4
    wss
    #
    @8
    @0
    @1
    @9
    @5
    @0
    @1
    wa
    @0
    @2
    cX
    wss
    cS
    @2
    wss
    @9
    @0
    @1
    simpl
    cS
    cJ
    cX
    clscld.1
    clsss3
    cS
    cJ
    cX
    clscld.1
    sscls
    @2
    cS
    cJ
    cX
    clscld.1
    ntrss
    syl3anc
    3adant3
    @5
    @0
    @9
    @8
    wb
    @1
    @4
    c0
    @7
    sseq2
    3ad2ant3
    mpbid
    @7
    ss0
    syl
end
