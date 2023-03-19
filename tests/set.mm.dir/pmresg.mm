include "wcel.mm"
include "cpm.mm"
include "co.mm"
include "wa.mm"
include "cvv.mm"
include "cdm.mm"
include "cin.mm"
include "cres.mm"
include "wf.mm"
include "c0.mm"
include "wceq.mm"
include "n0i.mm"
include "cxp.mm"
include "wfn.mm"
include "fnpm.mm"
include "fndm.mm"
include "ax-mp.mm"
include "ndmov.mm"
include "nsyl2.mm"
include "simpld.mm"
include "adantl.mm"
include "simpl.mm"
include "wss.mm"
include "elpmi.mm"
include "inss1.mm"
include "fssres.mm"
include "sylancl.mm"
include "wfun.mm"
include "ffun.mm"
include "resres.mm"
include "wrel.mm"
include "funrel.mm"
include "resdm.mm"
include "reseq1.mm"
include "3syl.mm"
include "syl5eqr.mm"
include "feq1d.mm"
include "mpbid.mm"
include "inss2.mm"
include "elpm2r.mm"
include "mpanr2.mm"
include "syl21anc.mm"

theorem pmresg
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F
  let cV: class V


  assert |- ( ( B e. V /\ F e. ( A ^pm C ) ) -> ( F |` B ) e. ( A ^pm B ) )

  proof
    cB
    cV
    wcel
    #
    cF
    cA
    cC
    cpm
    co
    #
    wcel
    #
    wa
    #
    cA
    cvv
    wcel
    #
    @0
    cF
    cdm
    #
    cB
    cin
    #
    cA
    cF
    cB
    cres
    #
    wf
    #
    @7
    cA
    cB
    cpm
    co
    wcel
    #
    @2
    @4
    @0
    @2
    @4
    cC
    cvv
    wcel
    #
    @2
    @1
    c0
    wceq
    @4
    @10
    wa
    @1
    cF
    n0i
    cA
    cC
    cvv
    cpm
    cpm
    cvv
    cvv
    cxp
    #
    wfn
    cpm
    cdm
    @11
    wceq
    fnpm
    @11
    cpm
    fndm
    ax-mp
    ndmov
    nsyl2
    simpld
    adantl
    @0
    @2
    simpl
    @3
    @6
    cA
    cF
    @6
    cres
    #
    wf
    #
    @8
    @3
    @5
    cA
    cF
    wf
    #
    @6
    @5
    wss
    @13
    @2
    @14
    @0
    @2
    @14
    @5
    cC
    wss
    cA
    cC
    cF
    elpmi
    simpld
    adantl
    #
    @5
    cB
    inss1
    @5
    cA
    @6
    cF
    fssres
    sylancl
    @3
    @6
    cA
    @12
    @7
    @3
    @14
    cF
    wfun
    #
    @12
    @7
    wceq
    @15
    @5
    cA
    cF
    ffun
    @16
    @12
    cF
    @5
    cres
    #
    cB
    cres
    #
    @7
    cF
    @5
    cB
    resres
    @16
    cF
    wrel
    @17
    cF
    wceq
    @18
    @7
    wceq
    cF
    funrel
    cF
    resdm
    @17
    cF
    cB
    reseq1
    3syl
    syl5eqr
    3syl
    feq1d
    mpbid
    @4
    @0
    wa
    @8
    @6
    cB
    wss
    @9
    @5
    cB
    inss2
    cA
    cB
    @6
    @7
    cvv
    cV
    elpm2r
    mpanr2
    syl21anc
end
