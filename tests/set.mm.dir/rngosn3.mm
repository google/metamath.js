include "crngo.mm"
include "wcel.mm"
include "wa.mm"
include "csn.mm"
include "wceq.mm"
include "c2nd.mm"
include "cfv.mm"
include "cop.mm"
include "c1st.mm"
include "cxp.mm"
include "wf.mm"
include "cgr.mm"
include "wfo.mm"
include "rngogrpo.mm"
include "grpofo.mm"
include "fof.mm"
include "3syl.mm"
include "adantr.mm"
include "id.mm"
include "sqxpeqd.mm"
include "feq23d.mm"
include "syl5ibcom.mm"
include "cdm.mm"
include "fdm.mm"
include "syl.mm"
include "eqcomd.mm"
include "eqeq2d.mm"
include "xpid11.mm"
include "syl6ib.mm"
include "impbid.mm"
include "simpr.mm"
include "xpsng.mm"
include "sylancom.mm"
include "feq2d.mm"
include "cvv.mm"
include "wb.mm"
include "opex.mm"
include "fsng.mm"
include "sylancr.mm"
include "3bitrd.mm"
include "eqeq1i.mm"
include "syl6bb.mm"
include "anbi1d.mm"
include "eqid.mm"
include "rngosm.mm"
include "bitrd.mm"
include "sylibd.mm"
include "pm4.71d.mm"
include "wrel.mm"
include "wss.mm"
include "relrngo.mm"
include "df-rel.mm"
include "mpbi.mm"
include "sseli.mm"
include "eqop.mm"
include "3bitr4d.mm"

theorem rngosn3
  let cA: class A
  let cB: class B
  let cR: class R
  let cG: class G
  let cX: class X
  assume on1el3.1: |- G = ( 1st ` R )
  assume on1el3.2: |- X = ran G


  assert |- ( ( R e. RingOps /\ A e. B ) -> ( X = { A } <-> R = <. { <. <. A , A >. , A >. } , { <. <. A , A >. , A >. } >. ) )

  proof
    cR
    crngo
    wcel
    #
    cA
    cB
    wcel
    #
    wa
    #
    cX
    cA
    csn
    #
    wceq
    #
    cR
    c2nd
    cfv
    #
    cA
    cA
    cop
    #
    cA
    cop
    csn
    #
    wceq
    #
    wa
    cR
    c1st
    cfv
    #
    @7
    wceq
    #
    @8
    wa
    #
    @4
    cR
    @7
    @7
    cop
    wceq
    #
    @2
    @4
    @10
    @8
    @2
    @4
    cG
    @7
    wceq
    #
    @10
    @2
    @4
    @3
    @3
    cxp
    #
    @3
    cG
    wf
    #
    @6
    csn
    #
    @3
    cG
    wf
    #
    @13
    @2
    @4
    @15
    @2
    cX
    cX
    cxp
    #
    cX
    cG
    wf
    #
    @4
    @15
    @0
    @19
    @1
    @0
    cG
    cgr
    wcel
    @18
    cX
    cG
    wfo
    @19
    cR
    cG
    on1el3.1
    rngogrpo
    cG
    cX
    on1el3.2
    grpofo
    @18
    cX
    cG
    fof
    3syl
    adantr
    #
    @4
    @18
    cX
    @14
    @3
    cG
    @4
    cX
    @3
    @4
    id
    #
    sqxpeqd
    #
    @21
    feq23d
    syl5ibcom
    @2
    @15
    @18
    @14
    wceq
    #
    @4
    @2
    @18
    cG
    cdm
    #
    wceq
    @15
    @23
    @2
    @24
    @18
    @2
    @19
    @24
    @18
    wceq
    @20
    @18
    cX
    cG
    fdm
    syl
    eqcomd
    @15
    @24
    @14
    @18
    @14
    @3
    cG
    fdm
    eqeq2d
    syl5ibcom
    cX
    @3
    xpid11
    syl6ib
    impbid
    @2
    @14
    @16
    @3
    cG
    @0
    @1
    @1
    @14
    @16
    wceq
    @0
    @1
    simpr
    #
    cA
    cA
    cB
    cB
    xpsng
    sylancom
    #
    feq2d
    @2
    @6
    cvv
    wcel
    #
    @1
    @17
    @13
    wb
    cA
    cA
    opex
    #
    @25
    @6
    cA
    cvv
    cB
    cG
    fsng
    sylancr
    3bitrd
    cG
    @9
    @7
    on1el3.1
    eqeq1i
    syl6bb
    anbi1d
    @2
    @4
    @8
    @2
    @4
    @14
    @3
    @5
    wf
    #
    @8
    @2
    @18
    cX
    @5
    wf
    #
    @4
    @29
    @0
    @30
    @1
    cR
    cG
    @5
    cX
    on1el3.1
    @5
    eqid
    on1el3.2
    rngosm
    adantr
    @4
    @18
    cX
    @14
    @3
    @5
    @22
    @21
    feq23d
    syl5ibcom
    @2
    @29
    @16
    @3
    @5
    wf
    #
    @8
    @2
    @14
    @16
    @3
    @5
    @26
    feq2d
    @2
    @27
    @1
    @31
    @8
    wb
    @28
    @25
    @6
    cA
    cvv
    cB
    @5
    fsng
    sylancr
    bitrd
    sylibd
    pm4.71d
    @2
    cR
    cvv
    cvv
    cxp
    #
    wcel
    #
    @12
    @11
    wb
    @0
    @33
    @1
    crngo
    @32
    cR
    crngo
    wrel
    crngo
    @32
    wss
    relrngo
    crngo
    df-rel
    mpbi
    sseli
    adantr
    cR
    @7
    @7
    cvv
    cvv
    eqop
    syl
    3bitr4d
end
