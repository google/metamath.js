include "com.mm"
include "wcel.mm"
include "c0.mm"
include "wne.mm"
include "wa.mm"
include "c1o.mm"
include "wss.mm"
include "csuc.mm"
include "cfinxp.mm"
include "cxp.mm"
include "wceq.mm"
include "word.mm"
include "wb.mm"
include "nnord.mm"
include "ordge1n0.mm"
include "syl.mm"
include "biimprd.mm"
include "imdistani.mm"
include "cvv.mm"
include "cv.mm"
include "cuni.mm"
include "c1st.mm"
include "cfv.mm"
include "cop.mm"
include "cif.mm"
include "cmpt2.mm"
include "eqid.mm"
include "finxpsuclem.mm"

theorem finxpsuc
  let cU: class U
  let cN: class N
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( N e. _om /\ N =/= (/) ) -> ( U ^^ suc N ) = ( ( U ^^ N ) X. U ) )

  proof
    cN
    com
    wcel
    #
    cN
    c0
    wne
    #
    wa
    @0
    c1o
    cN
    wss
    #
    wa
    cU
    cN
    csuc
    cfinxp
    cU
    cN
    cfinxp
    cU
    cxp
    wceq
    @0
    @1
    @2
    @0
    @2
    @1
    @0
    cN
    word
    @2
    @1
    wb
    cN
    nnord
    cN
    ordge1n0
    syl
    biimprd
    imdistani
    vx
    cU
    vy
    vy
    vx
    com
    cvv
    vy
    cv
    #
    c1o
    wceq
    vx
    cv
    #
    cU
    wcel
    wa
    c0
    @4
    cvv
    cU
    cxp
    wcel
    @3
    cuni
    @4
    c1st
    cfv
    cop
    @3
    @4
    cop
    cif
    cif
    cmpt2
    #
    cN
    @5
    eqid
    finxpsuclem
    syl
end
