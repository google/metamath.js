include "cumgr.mm"
include "wcel.mm"
include "cfv.mm"
include "cpr.mm"
include "wceq.mm"
include "wne.mm"
include "wi.mm"
include "cdm.mm"
include "csn.mm"
include "cres.mm"
include "wfun.mm"
include "wa.mm"
include "c0.mm"
include "prnzg.mm"
include "adantl.mm"
include "wb.mm"
include "neeq1.mm"
include "adantr.mm"
include "mpbird.mm"
include "fvfundmfvn0.mm"
include "syl.mm"
include "chash.mm"
include "c2.mm"
include "cvtx.mm"
include "eqid.mm"
include "umgredg2.mm"
include "fveq2.mm"
include "eqeq1d.mm"
include "hashprdifel.mm"
include "simp3d.mm"
include "syl6bi.mm"
include "syl5com.mm"
include "expcom.mm"
include "com23.mm"
include "mpcom.mm"
include "ex.mm"
include "com13.mm"
include "imp.mm"

theorem umgrnloopv
  let cE: class E
  let cG: class G
  let cM: class M
  let cN: class N
  let cW: class W
  let cX: class X
  assume umgrnloopv.e: |- E = ( iEdg ` G )


  assert |- ( ( G e. UMGraph /\ M e. W ) -> ( ( E ` X ) = { M , N } -> M =/= N ) )

  proof
    cG
    cumgr
    wcel
    #
    cM
    cW
    wcel
    #
    cX
    cE
    cfv
    #
    cM
    cN
    cpr
    #
    wceq
    #
    cM
    cN
    wne
    #
    wi
    @4
    @1
    @0
    @5
    @4
    @1
    @0
    @5
    wi
    #
    cX
    cE
    cdm
    wcel
    #
    cE
    cX
    csn
    cres
    wfun
    #
    wa
    #
    @4
    @1
    wa
    #
    @6
    @10
    @2
    c0
    wne
    #
    @9
    @10
    @11
    @3
    c0
    wne
    #
    @1
    @12
    @4
    cM
    cN
    cW
    prnzg
    adantl
    @4
    @11
    @12
    wb
    @1
    @2
    @3
    c0
    neeq1
    adantr
    mpbird
    cX
    cE
    fvfundmfvn0
    syl
    @7
    @10
    @6
    wi
    @8
    @7
    @0
    @10
    @5
    @0
    @7
    @10
    @5
    wi
    @0
    @7
    wa
    @2
    chash
    cfv
    #
    c2
    wceq
    #
    @10
    @5
    cE
    cG
    cG
    cvtx
    cfv
    #
    cX
    @15
    eqid
    umgrnloopv.e
    umgredg2
    @4
    @14
    @5
    wi
    @1
    @4
    @14
    @3
    chash
    cfv
    #
    c2
    wceq
    #
    @5
    @4
    @13
    @16
    c2
    @2
    @3
    chash
    fveq2
    eqeq1d
    @17
    cM
    @3
    wcel
    cN
    @3
    wcel
    @5
    cM
    cN
    @3
    @3
    eqid
    hashprdifel
    simp3d
    syl6bi
    adantr
    syl5com
    expcom
    com23
    adantr
    mpcom
    ex
    com13
    imp
end
