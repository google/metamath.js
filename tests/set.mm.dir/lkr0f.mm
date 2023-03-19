include "clmod.mm"
include "wcel.mm"
include "wa.mm"
include "cfv.mm"
include "wceq.mm"
include "csn.mm"
include "cxp.mm"
include "wfn.mm"
include "ccnv.mm"
include "cima.mm"
include "cbs.mm"
include "wf.mm"
include "eqid.mm"
include "lflf.mm"
include "ffn.mm"
include "syl.mm"
include "adantr.mm"
include "lkrval.mm"
include "eqeq1d.mm"
include "biimpa.mm"
include "c0g.mm"
include "cvv.mm"
include "fvex.mm"
include "eqeltri.mm"
include "fconst2.mm"
include "fconst4.mm"
include "bitr3i.mm"
include "sylanbrc.mm"
include "ex.mm"
include "wi.mm"
include "biimpi.mm"
include "adantl.mm"
include "clfn.mm"
include "simpr.mm"
include "lfl0f.mm"
include "eqeltrd.mm"
include "syldan.mm"
include "sylbir.mm"
include "biantrurd.mm"
include "bitrd.mm"
include "mpbird.mm"
include "impbid.mm"

theorem lkr0f
  let cD: class D
  let cF: class F
  let cG: class G
  let cK: class K
  let cV: class V
  let cW: class W
  let c.0: class .0.
  assume lkr0f.d: |- D = ( Scalar ` W )
  assume lkr0f.o: |- .0. = ( 0g ` D )
  assume lkr0f.v: |- V = ( Base ` W )
  assume lkr0f.f: |- F = ( LFnl ` W )
  assume lkr0f.k: |- K = ( LKer ` W )


  assert |- ( ( W e. LMod /\ G e. F ) -> ( ( K ` G ) = V <-> G = ( V X. { .0. } ) ) )

  proof
    cW
    clmod
    wcel
    #
    cG
    cF
    wcel
    #
    wa
    #
    cG
    cK
    cfv
    #
    cV
    wceq
    #
    cG
    cV
    c.0
    csn
    #
    cxp
    #
    wceq
    #
    @2
    @4
    @7
    @2
    @4
    wa
    cG
    cV
    wfn
    #
    cG
    ccnv
    @5
    cima
    #
    cV
    wceq
    #
    @7
    @2
    @8
    @4
    @2
    cV
    cD
    cbs
    cfv
    #
    cG
    wf
    @8
    cD
    cF
    cG
    @11
    cV
    cW
    clmod
    lkr0f.d
    @11
    eqid
    lkr0f.v
    lkr0f.f
    lflf
    cV
    @11
    cG
    ffn
    syl
    adantr
    @2
    @4
    @10
    @2
    @3
    @9
    cV
    cD
    cF
    cG
    cK
    cW
    clmod
    c.0
    lkr0f.d
    lkr0f.o
    lkr0f.f
    lkr0f.k
    lkrval
    eqeq1d
    biimpa
    @7
    cV
    @5
    cG
    wf
    #
    @8
    @10
    wa
    #
    cV
    c.0
    cG
    c.0
    cD
    c0g
    cfv
    cvv
    lkr0f.o
    cD
    c0g
    fvex
    eqeltri
    fconst2
    #
    cV
    c.0
    cG
    fconst4
    bitr3i
    #
    sylanbrc
    ex
    @0
    @7
    @4
    wi
    @1
    @0
    @7
    @4
    @0
    @7
    wa
    #
    @4
    @13
    @7
    @13
    @0
    @7
    @13
    @15
    biimpi
    adantl
    @16
    @4
    @10
    @13
    @16
    @3
    @9
    cV
    @0
    @7
    cG
    cW
    clfn
    cfv
    #
    wcel
    @3
    @9
    wceq
    @16
    cG
    @6
    @17
    @0
    @7
    simpr
    @0
    @6
    @17
    wcel
    @7
    cD
    @17
    cV
    cW
    c.0
    lkr0f.d
    lkr0f.o
    lkr0f.v
    @17
    eqid
    #
    lfl0f
    adantr
    eqeltrd
    cD
    @17
    cG
    cK
    cW
    clmod
    c.0
    lkr0f.d
    lkr0f.o
    @18
    lkr0f.k
    lkrval
    syldan
    eqeq1d
    @16
    @8
    @10
    @7
    @8
    @0
    @7
    @12
    @8
    @14
    cV
    @5
    cG
    ffn
    sylbir
    adantl
    biantrurd
    bitrd
    mpbird
    ex
    adantr
    impbid
end
