include "c1.mm"
include "cfz.mm"
include "co.mm"
include "cmap.mm"
include "wcel.mm"
include "wa.mm"
include "cvv.mm"
include "cdm.mm"
include "wn.mm"
include "cop.mm"
include "csn.mm"
include "cun.mm"
include "cfv.mm"
include "wceq.mm"
include "caddc.mm"
include "ovex.mm"
include "eqeltri.mm"
include "a1i.mm"
include "elex.mm"
include "adantl.mm"
include "cin.mm"
include "c0.mm"
include "wf.mm"
include "elmapi.mm"
include "fdm.mm"
include "syl.mm"
include "adantr.mm"
include "ineq1d.mm"
include "sneqi.mm"
include "ineq2i.mm"
include "fzp1disj.mm"
include "eqtri.mm"
include "syl6eq.mm"
include "disjsn.mm"
include "sylib.mm"
include "fsnunfv.mm"
include "syl3anc.mm"

theorem mapfzcons2
  let cA: class A
  let cB: class B
  let cC: class C
  let cM: class M
  let cN: class N
  assume mapfzcons.1: |- M = ( N + 1 )


  assert |- ( ( A e. ( B ^m ( 1 ... N ) ) /\ C e. B ) -> ( ( A u. { <. M , C >. } ) ` M ) = C )

  proof
    cA
    cB
    c1
    cN
    cfz
    co
    #
    cmap
    co
    wcel
    #
    cC
    cB
    wcel
    #
    wa
    #
    cM
    cvv
    wcel
    #
    cC
    cvv
    wcel
    #
    cM
    cA
    cdm
    #
    wcel
    wn
    #
    cM
    cA
    cM
    cC
    cop
    csn
    cun
    cfv
    cC
    wceq
    @4
    @3
    cM
    cN
    c1
    caddc
    co
    #
    cvv
    mapfzcons.1
    cN
    c1
    caddc
    ovex
    eqeltri
    a1i
    @2
    @5
    @1
    cC
    cB
    elex
    adantl
    @3
    @6
    cM
    csn
    #
    cin
    #
    c0
    wceq
    @7
    @3
    @10
    @0
    @9
    cin
    #
    c0
    @3
    @6
    @0
    @9
    @1
    @6
    @0
    wceq
    #
    @2
    @1
    @0
    cB
    cA
    wf
    @12
    cA
    cB
    @0
    elmapi
    @0
    cB
    cA
    fdm
    syl
    adantr
    ineq1d
    @11
    @0
    @8
    csn
    #
    cin
    c0
    @9
    @13
    @0
    cM
    @8
    mapfzcons.1
    sneqi
    ineq2i
    c1
    cN
    fzp1disj
    eqtri
    syl6eq
    @6
    cM
    disjsn
    sylib
    cA
    cvv
    cvv
    cM
    cC
    fsnunfv
    syl3anc
end
