include "wfn.mm"
include "wcel.mm"
include "wn.mm"
include "wa.mm"
include "cres.mm"
include "cop.mm"
include "csn.mm"
include "cun.mm"
include "c0.mm"
include "wceq.mm"
include "fnresdm.mm"
include "adantr.mm"
include "ressnop0.mm"
include "adantl.mm"
include "uneq12d.mm"
include "resundir.mm"
include "un0.mm"
include "eqcomi.mm"
include "3eqtr4g.mm"

theorem fsnunres
  let cS: class S
  let cF: class F
  let cX: class X
  let cY: class Y


  assert |- ( ( F Fn S /\ -. X e. S ) -> ( ( F u. { <. X , Y >. } ) |` S ) = F )

  proof
    cF
    cS
    wfn
    #
    cX
    cS
    wcel
    wn
    #
    wa
    #
    cF
    cS
    cres
    #
    cX
    cY
    cop
    csn
    #
    cS
    cres
    #
    cun
    cF
    c0
    cun
    #
    cF
    @4
    cun
    cS
    cres
    cF
    @2
    @3
    cF
    @5
    c0
    @0
    @3
    cF
    wceq
    @1
    cS
    cF
    fnresdm
    adantr
    @1
    @5
    c0
    wceq
    @0
    cX
    cY
    cS
    ressnop0
    adantl
    uneq12d
    cF
    @4
    cS
    resundir
    @6
    cF
    cF
    un0
    eqcomi
    3eqtr4g
end
