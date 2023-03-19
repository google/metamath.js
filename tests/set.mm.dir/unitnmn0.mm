include "cnrg.mm"
include "wcel.mm"
include "cnzr.mm"
include "w3a.mm"
include "cngp.mm"
include "cbs.mm"
include "cfv.mm"
include "c0g.mm"
include "wne.mm"
include "cc0.mm"
include "nrgngp.mm"
include "3ad2ant1.mm"
include "eqid.mm"
include "unitcl.mm"
include "3ad2ant3.mm"
include "nzrunit.mm"
include "3adant1.mm"
include "nmne0.mm"
include "syl3anc.mm"

theorem unitnmn0
  let cA: class A
  let cR: class R
  let cU: class U
  let cN: class N
  assume nminvr.n: |- N = ( norm ` R )
  assume nminvr.u: |- U = ( Unit ` R )


  assert |- ( ( R e. NrmRing /\ R e. NzRing /\ A e. U ) -> ( N ` A ) =/= 0 )

  proof
    cR
    cnrg
    wcel
    #
    cR
    cnzr
    wcel
    #
    cA
    cU
    wcel
    #
    w3a
    cR
    cngp
    wcel
    #
    cA
    cR
    cbs
    cfv
    #
    wcel
    #
    cA
    cR
    c0g
    cfv
    #
    wne
    #
    cA
    cN
    cfv
    cc0
    wne
    @0
    @1
    @3
    @2
    cR
    nrgngp
    3ad2ant1
    @2
    @0
    @5
    @1
    @4
    cR
    cU
    cA
    @4
    eqid
    #
    nminvr.u
    unitcl
    3ad2ant3
    @1
    @2
    @7
    @0
    cA
    cR
    cU
    @6
    nminvr.u
    @6
    eqid
    #
    nzrunit
    3adant1
    cA
    cR
    cN
    @4
    @6
    @8
    nminvr.n
    @9
    nmne0
    syl3anc
end
