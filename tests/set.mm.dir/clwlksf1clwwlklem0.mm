include "wcel.mm"
include "cclwlks.mm"
include "cfv.mm"
include "c1st.mm"
include "chash.mm"
include "wceq.mm"
include "wa.mm"
include "ciedg.mm"
include "cdm.mm"
include "cword.mm"
include "cc0.mm"
include "cfz.mm"
include "co.mm"
include "cvtx.mm"
include "c2nd.mm"
include "wf.mm"
include "w3a.mm"
include "cv.mm"
include "fveq2.mm"
include "syl5eq.mm"
include "fveq2d.mm"
include "eqeq1d.mm"
include "elrab2.mm"
include "c1.mm"
include "caddc.mm"
include "csn.mm"
include "cpr.mm"
include "wss.mm"
include "wif.mm"
include "cfzo.mm"
include "wral.mm"
include "eqid.mm"
include "clwlkcompim.mm"
include "simpr.mm"
include "anim2i.mm"
include "df-3an.mm"
include "sylibr.mm"
include "syl.mm"
include "anim1i.mm"
include "sylbi.mm"

theorem clwlksf1clwwlklem0
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F
  let cG: class G
  let cN: class N
  let cW: class W
  let vc: setvar c
  let vi: setvar i
  let vx: setvar x
  let vf: setvar f
  let vw: setvar w
  assume clwlksfclwwlk.1: |- A = ( 1st ` c )
  assume clwlksfclwwlk.2: |- B = ( 2nd ` c )
  assume clwlksfclwwlk.c: |- C = { c e. ( ClWalks ` G ) | ( # ` A ) = N }
  assume clwlksfclwwlk.f: |- F = ( c e. C |-> ( B substr <. 0 , ( # ` A ) >. ) )

  disjoint G c
  disjoint N c
  disjoint W c
  disjoint C c
  disjoint F c
  disjoint A i
  disjoint B i
  disjoint G i
  disjoint c i
  disjoint C i
  disjoint G x
  disjoint i x
  disjoint N i
  disjoint C f
  disjoint C w
  disjoint f w
  disjoint F f
  disjoint F w
  disjoint c f
  disjoint c w
  disjoint G f
  disjoint G w
  disjoint N f
  disjoint N w
  disjoint W i
  assert |- ( W e. C -> ( ( ( 1st ` W ) e. Word dom ( iEdg ` G ) /\ ( 2nd ` W ) : ( 0 ... ( # ` ( 1st ` W ) ) ) --> ( Vtx ` G ) /\ ( ( 2nd ` W ) ` 0 ) = ( ( 2nd ` W ) ` ( # ` ( 1st ` W ) ) ) ) /\ ( # ` ( 1st ` W ) ) = N ) )

  proof
    cW
    cC
    wcel
    cW
    cG
    cclwlks
    cfv
    #
    wcel
    #
    cW
    c1st
    cfv
    #
    chash
    cfv
    #
    cN
    wceq
    #
    wa
    @2
    cG
    ciedg
    cfv
    #
    cdm
    cword
    wcel
    #
    cc0
    @3
    cfz
    co
    cG
    cvtx
    cfv
    #
    cW
    c2nd
    cfv
    #
    wf
    #
    cc0
    @8
    cfv
    @3
    @8
    cfv
    wceq
    #
    w3a
    #
    @4
    wa
    cA
    chash
    cfv
    #
    cN
    wceq
    @4
    vc
    cW
    @0
    cC
    vc
    cv
    #
    cW
    wceq
    #
    @12
    @3
    cN
    @14
    cA
    @2
    chash
    @14
    cA
    @13
    c1st
    cfv
    @2
    clwlksfclwwlk.1
    @13
    cW
    c1st
    fveq2
    syl5eq
    fveq2d
    eqeq1d
    clwlksfclwwlk.c
    elrab2
    @1
    @11
    @4
    @1
    @6
    @9
    wa
    #
    vi
    cv
    #
    @8
    cfv
    #
    @16
    c1
    caddc
    co
    @8
    cfv
    #
    wceq
    @16
    @2
    cfv
    @5
    cfv
    #
    @17
    csn
    wceq
    @17
    @18
    cpr
    @19
    wss
    wif
    vi
    cc0
    @3
    cfzo
    co
    wral
    #
    @10
    wa
    #
    wa
    #
    @11
    @8
    vi
    @2
    cG
    @5
    @7
    cW
    @7
    eqid
    @5
    eqid
    @2
    eqid
    @8
    eqid
    clwlkcompim
    @22
    @15
    @10
    wa
    @11
    @21
    @10
    @15
    @20
    @10
    simpr
    anim2i
    @6
    @9
    @10
    df-3an
    sylibr
    syl
    anim1i
    sylbi
end
