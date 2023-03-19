include "c1.mm"
include "cfz.mm"
include "co.mm"
include "cmap.mm"
include "wcel.mm"
include "cres.mm"
include "cop.mm"
include "csn.mm"
include "cun.mm"
include "wf.mm"
include "wfn.mm"
include "wceq.mm"
include "elmapi.mm"
include "ffn.mm"
include "fnresdm.mm"
include "3syl.mm"
include "uneq1d.mm"
include "resundir.mm"
include "c0.mm"
include "cdm.mm"
include "cin.mm"
include "dmres.mm"
include "caddc.mm"
include "wss.mm"
include "dmsnopss.mm"
include "sneqi.mm"
include "sseqtri.mm"
include "sslin.mm"
include "ax-mp.mm"
include "fzp1disj.mm"
include "sseq0.mm"
include "mp2an.mm"
include "eqtri.mm"
include "wrel.mm"
include "wb.mm"
include "relres.mm"
include "reldm0.mm"
include "mpbir.mm"
include "uneq2i.mm"
include "un0.mm"
include "eqtr2i.mm"
include "3eqtr4g.mm"

theorem mapfzcons1
  let cA: class A
  let cB: class B
  let cC: class C
  let cM: class M
  let cN: class N
  assume mapfzcons.1: |- M = ( N + 1 )


  assert |- ( A e. ( B ^m ( 1 ... N ) ) -> ( ( A u. { <. M , C >. } ) |` ( 1 ... N ) ) = A )

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
    cA
    @0
    cres
    #
    cM
    cC
    cop
    csn
    #
    @0
    cres
    #
    cun
    cA
    @4
    cun
    #
    cA
    @3
    cun
    @0
    cres
    cA
    @1
    @2
    cA
    @4
    @1
    @0
    cB
    cA
    wf
    cA
    @0
    wfn
    @2
    cA
    wceq
    cA
    cB
    @0
    elmapi
    @0
    cB
    cA
    ffn
    @0
    cA
    fnresdm
    3syl
    uneq1d
    cA
    @3
    @0
    resundir
    @5
    cA
    c0
    cun
    cA
    @4
    c0
    cA
    @4
    c0
    wceq
    #
    @4
    cdm
    #
    c0
    wceq
    #
    @7
    @0
    @3
    cdm
    #
    cin
    #
    c0
    @3
    @0
    dmres
    @10
    @0
    cN
    c1
    caddc
    co
    #
    csn
    #
    cin
    #
    wss
    #
    @13
    c0
    wceq
    @10
    c0
    wceq
    @9
    @12
    wss
    @14
    @9
    cM
    csn
    @12
    cM
    cC
    dmsnopss
    cM
    @11
    mapfzcons.1
    sneqi
    sseqtri
    @9
    @12
    @0
    sslin
    ax-mp
    c1
    cN
    fzp1disj
    @10
    @13
    sseq0
    mp2an
    eqtri
    @4
    wrel
    @6
    @8
    wb
    @3
    @0
    relres
    @4
    reldm0
    ax-mp
    mpbir
    uneq2i
    cA
    un0
    eqtr2i
    3eqtr4g
end
