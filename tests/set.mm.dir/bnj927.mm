include "cv.mm"
include "csuc.mm"
include "wceq.mm"
include "wfn.mm"
include "wa.mm"
include "csn.mm"
include "cun.mm"
include "cop.mm"
include "cin.mm"
include "c0.mm"
include "simpr.mm"
include "vex.mm"
include "fnsn.mm"
include "a1i.mm"
include "bnj521.mm"
include "fnun.mm"
include "syl21anc.mm"
include "fneq1i.mm"
include "sylibr.mm"
include "df-suc.mm"
include "eqeq2i.mm"
include "biimpi.mm"
include "adantr.mm"
include "fneq2d.mm"
include "mpbird.mm"

theorem bnj927
  let cC: class C
  let vf: setvar f
  let vn: setvar n
  let cG: class G
  let vp: setvar p
  assume bnj927.1: |- G = ( f u. { <. n , C >. } )
  assume bnj927.2: |- C e. _V


  assert |- ( ( p = suc n /\ f Fn n ) -> G Fn p )

  proof
    vp
    cv
    #
    vn
    cv
    #
    csuc
    #
    wceq
    #
    vf
    cv
    #
    @1
    wfn
    #
    wa
    #
    cG
    @0
    wfn
    cG
    @1
    @1
    csn
    #
    cun
    #
    wfn
    #
    @6
    @4
    @1
    cC
    cop
    csn
    #
    cun
    #
    @8
    wfn
    #
    @9
    @6
    @5
    @10
    @7
    wfn
    #
    @1
    @7
    cin
    c0
    wceq
    #
    @12
    @3
    @5
    simpr
    @13
    @6
    @1
    cC
    vn
    vex
    bnj927.2
    fnsn
    a1i
    @14
    @6
    @1
    bnj521
    a1i
    @1
    @7
    @4
    @10
    fnun
    syl21anc
    @8
    cG
    @11
    bnj927.1
    fneq1i
    sylibr
    @6
    @0
    @8
    cG
    @3
    @0
    @8
    wceq
    #
    @5
    @3
    @15
    @2
    @8
    @0
    @1
    df-suc
    eqeq2i
    biimpi
    adantr
    fneq2d
    mpbird
end
