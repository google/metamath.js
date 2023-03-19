include "wceq.mm"
include "cuni.mm"
include "cin.mm"
include "cdm.mm"
include "wss.mm"
include "ccl.mm"
include "cfv.mm"
include "ctop.mm"
include "wcel.mm"
include "ccn.mm"
include "co.mm"
include "cntop1.mm"
include "syl.mm"
include "dmin.mm"
include "wf.mm"
include "eqid.mm"
include "cnf.mm"
include "fdm.mm"
include "3syl.mm"
include "ineq12d.mm"
include "inidm.mm"
include "syl6eq.mm"
include "syl5sseq.mm"
include "cres.mm"
include "wfn.mm"
include "wb.mm"
include "ffn.mm"
include "syl6sseq.mm"
include "fnreseql.mm"
include "syl3anc.mm"
include "mpbid.mm"
include "clsss.mm"
include "ccld.mm"
include "hauseqlcld.mm"
include "cldcls.mm"
include "3sstr3d.mm"
include "syl5eqssr.mm"
include "fneqeql2.mm"
include "syl2anc.mm"
include "mpbird.mm"

theorem hauseqcn
  let wph: wff ph
  let cA: class A
  let cF: class F
  let cG: class G
  let cJ: class J
  let cK: class K
  let cX: class X
  assume hauseqcn.x: |- X = U. J
  assume hauseqcn.k: |- ( ph -> K e. Haus )
  assume hauseqcn.f: |- ( ph -> F e. ( J Cn K ) )
  assume hauseqcn.g: |- ( ph -> G e. ( J Cn K ) )
  assume hauseqcn.e: |- ( ph -> ( F |` A ) = ( G |` A ) )
  assume hauseqcn.a: |- ( ph -> A C_ X )
  assume hauseqcn.c: |- ( ph -> ( ( cls ` J ) ` A ) = X )


  assert |- ( ph -> F = G )

  proof
    wph
    cF
    cG
    wceq
    #
    cJ
    cuni
    #
    cF
    cG
    cin
    cdm
    #
    wss
    #
    wph
    @1
    cX
    @2
    hauseqcn.x
    wph
    cA
    cJ
    ccl
    cfv
    #
    cfv
    #
    @2
    @4
    cfv
    #
    cX
    @2
    wph
    cJ
    ctop
    wcel
    #
    @2
    @1
    wss
    cA
    @2
    wss
    #
    @5
    @6
    wss
    wph
    cF
    cJ
    cK
    ccn
    co
    #
    wcel
    #
    @7
    hauseqcn.f
    cF
    cJ
    cK
    cntop1
    syl
    wph
    cF
    cdm
    #
    cG
    cdm
    #
    cin
    #
    @2
    @1
    cF
    cG
    dmin
    wph
    @13
    @1
    @1
    cin
    @1
    wph
    @11
    @1
    @12
    @1
    wph
    @10
    @1
    cK
    cuni
    #
    cF
    wf
    #
    @11
    @1
    wceq
    hauseqcn.f
    cF
    cJ
    cK
    @1
    @14
    @1
    eqid
    #
    @14
    eqid
    #
    cnf
    #
    @1
    @14
    cF
    fdm
    3syl
    wph
    cG
    @9
    wcel
    #
    @1
    @14
    cG
    wf
    #
    @12
    @1
    wceq
    hauseqcn.g
    cG
    cJ
    cK
    @1
    @14
    @16
    @17
    cnf
    #
    @1
    @14
    cG
    fdm
    3syl
    ineq12d
    @1
    inidm
    syl6eq
    syl5sseq
    wph
    cF
    cA
    cres
    cG
    cA
    cres
    wceq
    #
    @8
    hauseqcn.e
    wph
    cF
    @1
    wfn
    #
    cG
    @1
    wfn
    #
    cA
    @1
    wss
    @22
    @8
    wb
    wph
    @10
    @15
    @23
    hauseqcn.f
    @18
    @1
    @14
    cF
    ffn
    3syl
    #
    wph
    @19
    @20
    @24
    hauseqcn.g
    @21
    @1
    @14
    cG
    ffn
    3syl
    #
    wph
    cA
    cX
    @1
    hauseqcn.a
    hauseqcn.x
    syl6sseq
    @1
    cF
    cG
    cA
    fnreseql
    syl3anc
    mpbid
    @2
    cA
    cJ
    @1
    @16
    clsss
    syl3anc
    hauseqcn.c
    wph
    @2
    cJ
    ccld
    cfv
    wcel
    @6
    @2
    wceq
    wph
    cF
    cG
    cJ
    cK
    hauseqcn.k
    hauseqcn.f
    hauseqcn.g
    hauseqlcld
    @2
    cJ
    cldcls
    syl
    3sstr3d
    syl5eqssr
    wph
    @23
    @24
    @0
    @3
    wb
    @25
    @26
    @1
    cF
    cG
    fneqeql2
    syl2anc
    mpbird
end
