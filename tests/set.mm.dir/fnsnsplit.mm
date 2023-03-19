include "wfn.mm"
include "wcel.mm"
include "wa.mm"
include "cres.mm"
include "csn.mm"
include "cdif.mm"
include "cfv.mm"
include "cop.mm"
include "cun.mm"
include "wceq.mm"
include "fnresdm.mm"
include "adantr.mm"
include "resundi.mm"
include "difsnid.mm"
include "adantl.mm"
include "reseq2d.mm"
include "fnressn.mm"
include "uneq2d.mm"
include "3eqtr3a.mm"
include "eqtr3d.mm"

theorem fnsnsplit
  let cA: class A
  let cF: class F
  let cX: class X


  assert |- ( ( F Fn A /\ X e. A ) -> F = ( ( F |` ( A \ { X } ) ) u. { <. X , ( F ` X ) >. } ) )

  proof
    cF
    cA
    wfn
    #
    cX
    cA
    wcel
    #
    wa
    #
    cF
    cA
    cres
    #
    cF
    cF
    cA
    cX
    csn
    #
    cdif
    #
    cres
    #
    cX
    cX
    cF
    cfv
    cop
    csn
    #
    cun
    #
    @0
    @3
    cF
    wceq
    @1
    cA
    cF
    fnresdm
    adantr
    @2
    cF
    @5
    @4
    cun
    #
    cres
    @6
    cF
    @4
    cres
    #
    cun
    @3
    @8
    cF
    @5
    @4
    resundi
    @2
    @9
    cA
    cF
    @1
    @9
    cA
    wceq
    @0
    cA
    cX
    difsnid
    adantl
    reseq2d
    @2
    @10
    @7
    @6
    cA
    cX
    cF
    fnressn
    uneq2d
    3eqtr3a
    eqtr3d
end
