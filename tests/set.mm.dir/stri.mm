include "cv.mm"
include "cfv.mm"
include "c1.mm"
include "wceq.mm"
include "wi.mm"
include "cst.mm"
include "wral.mm"
include "wn.mm"
include "wrex.mm"
include "wss.mm"
include "dfral2.mm"
include "cno.mm"
include "cdif.mm"
include "strlem1.mm"
include "wcel.mm"
include "wa.mm"
include "cch.mm"
include "cpjh.mm"
include "c2.mm"
include "cexp.mm"
include "co.mm"
include "cmpt.mm"
include "eqid.mm"
include "biid.mm"
include "strlem3.mm"
include "strlem6.mm"
include "fveq1.mm"
include "eqeq1d.mm"
include "imbi12d.mm"
include "notbid.mm"
include "rspcev.mm"
include "syl2anc.mm"
include "rexlimiva.mm"
include "syl.mm"
include "con1i.mm"
include "sylbi.mm"

theorem stri
  let cA: class A
  let cB: class B
  let vf: setvar f
  let vu: setvar u
  let vx: setvar x
  assume str.1: |- A e. CH
  assume str.2: |- B e. CH

  disjoint A f
  disjoint B f
  disjoint u x
  disjoint f x
  disjoint A x
  disjoint f u
  disjoint A u
  disjoint B x
  disjoint B u
  assert |- ( A. f e. States ( ( f ` A ) = 1 -> ( f ` B ) = 1 ) -> A C_ B )

  proof
    cA
    vf
    cv
    #
    cfv
    #
    c1
    wceq
    #
    cB
    @0
    cfv
    #
    c1
    wceq
    #
    wi
    #
    vf
    cst
    wral
    @5
    wn
    #
    vf
    cst
    wrex
    #
    wn
    cA
    cB
    wss
    #
    @5
    vf
    cst
    dfral2
    @8
    @7
    @8
    wn
    vu
    cv
    #
    cno
    cfv
    c1
    wceq
    #
    vu
    cA
    cB
    cdif
    #
    wrex
    @7
    vu
    cA
    cB
    str.1
    str.2
    strlem1
    @10
    @7
    vu
    @11
    @9
    @11
    wcel
    @10
    wa
    #
    vx
    cch
    @9
    vx
    cv
    cpjh
    cfv
    cfv
    cno
    cfv
    c2
    cexp
    co
    cmpt
    #
    cst
    wcel
    cA
    @13
    cfv
    #
    c1
    wceq
    #
    cB
    @13
    cfv
    #
    c1
    wceq
    #
    wi
    #
    wn
    #
    @7
    @12
    vx
    vu
    cA
    cB
    @13
    @13
    eqid
    #
    @12
    biid
    #
    str.1
    str.2
    strlem3
    @12
    vx
    vu
    cA
    cB
    @13
    @20
    @21
    str.1
    str.2
    strlem6
    @6
    @19
    vf
    @13
    cst
    @0
    @13
    wceq
    #
    @5
    @18
    @22
    @2
    @15
    @4
    @17
    @22
    @1
    @14
    c1
    cA
    @0
    @13
    fveq1
    eqeq1d
    @22
    @3
    @16
    c1
    cB
    @0
    @13
    fveq1
    eqeq1d
    imbi12d
    notbid
    rspcev
    syl2anc
    rexlimiva
    syl
    con1i
    sylbi
end
