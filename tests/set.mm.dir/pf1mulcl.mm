include "wcel.mm"
include "wa.mm"
include "cbs.mm"
include "cfv.mm"
include "cpws.mm"
include "co.mm"
include "cmulr.mm"
include "cof.mm"
include "ccrg.mm"
include "cvv.mm"
include "eqid.mm"
include "pf1rcl.mm"
include "adantr.mm"
include "fvexd.mm"
include "wf.mm"
include "pf1f.mm"
include "wb.mm"
include "fvex.mm"
include "pwselbasb.mm"
include "sylancl.mm"
include "mpbird.mm"
include "adantl.mm"
include "pwsmulrval.mm"
include "csubrg.mm"
include "pf1subrg.mm"
include "syl.mm"
include "subrgmcl.mm"
include "3expib.mm"
include "mpcom.mm"
include "eqeltrrd.mm"

theorem pf1mulcl
  let cQ: class Q
  let cR: class R
  let c.x: class .x.
  let cF: class F
  let cG: class G
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cB: class B
  let cE: class E
  assume pf1rcl.q: |- Q = ran ( eval1 ` R )
  assume pf1mulcl.t: |- .x. = ( .r ` R )


  assert |- ( ( F e. Q /\ G e. Q ) -> ( F oF .x. G ) e. Q )

  proof
    cF
    cQ
    wcel
    #
    cG
    cQ
    wcel
    #
    wa
    #
    cF
    cG
    cR
    cR
    cbs
    cfv
    #
    cpws
    co
    #
    cmulr
    cfv
    #
    co
    #
    cF
    cG
    c.x
    cof
    co
    cQ
    @2
    @4
    cbs
    cfv
    #
    cR
    @5
    c.x
    cF
    cG
    @3
    ccrg
    cvv
    @4
    @4
    eqid
    #
    @7
    eqid
    #
    @0
    cR
    ccrg
    wcel
    #
    @1
    cQ
    cR
    cF
    pf1rcl.q
    pf1rcl
    adantr
    #
    @2
    cR
    cbs
    fvexd
    @2
    cF
    @7
    wcel
    #
    @3
    @3
    cF
    wf
    #
    @0
    @13
    @1
    @3
    cQ
    cR
    cF
    pf1rcl.q
    @3
    eqid
    #
    pf1f
    adantr
    @2
    @10
    @3
    cvv
    wcel
    #
    @12
    @13
    wb
    @11
    cR
    cbs
    fvex
    #
    @3
    cR
    @3
    @7
    ccrg
    cF
    @4
    cvv
    @8
    @14
    @9
    pwselbasb
    sylancl
    mpbird
    @2
    cG
    @7
    wcel
    #
    @3
    @3
    cG
    wf
    #
    @1
    @18
    @0
    @3
    cQ
    cR
    cG
    pf1rcl.q
    @14
    pf1f
    adantl
    @2
    @10
    @15
    @17
    @18
    wb
    @11
    @16
    @3
    cR
    @3
    @7
    ccrg
    cG
    @4
    cvv
    @8
    @14
    @9
    pwselbasb
    sylancl
    mpbird
    pf1mulcl.t
    @5
    eqid
    #
    pwsmulrval
    cQ
    @4
    csubrg
    cfv
    wcel
    #
    @2
    @6
    cQ
    wcel
    #
    @2
    @10
    @20
    @11
    @3
    cQ
    cR
    @14
    pf1rcl.q
    pf1subrg
    syl
    @20
    @0
    @1
    @21
    cQ
    @4
    @5
    cF
    cG
    @19
    subrgmcl
    3expib
    mpcom
    eqeltrrd
end
