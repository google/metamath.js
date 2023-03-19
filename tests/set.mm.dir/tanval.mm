include "cc.mm"
include "wcel.mm"
include "ccos.mm"
include "cfv.mm"
include "cc0.mm"
include "wne.mm"
include "wa.mm"
include "ccnv.mm"
include "csn.mm"
include "cdif.mm"
include "cima.mm"
include "ctan.mm"
include "csin.mm"
include "cdiv.mm"
include "co.mm"
include "wceq.mm"
include "simpl.mm"
include "coscl.mm"
include "anim1i.mm"
include "eldifsn.mm"
include "sylibr.mm"
include "wf.mm"
include "wfn.mm"
include "wb.mm"
include "cosf.mm"
include "ffn.mm"
include "elpreima.mm"
include "mp2b.mm"
include "sylanbrc.mm"
include "cv.mm"
include "fveq2.mm"
include "oveq12d.mm"
include "df-tan.mm"
include "ovex.mm"
include "fvmpt.mm"
include "syl.mm"

theorem tanval
  let cA: class A
  let vx: setvar x


  assert |- ( ( A e. CC /\ ( cos ` A ) =/= 0 ) -> ( tan ` A ) = ( ( sin ` A ) / ( cos ` A ) ) )

  proof
    cA
    cc
    wcel
    #
    cA
    ccos
    cfv
    #
    cc0
    wne
    #
    wa
    #
    cA
    ccos
    ccnv
    cc
    cc0
    csn
    cdif
    #
    cima
    #
    wcel
    #
    cA
    ctan
    cfv
    cA
    csin
    cfv
    #
    @1
    cdiv
    co
    #
    wceq
    @3
    @0
    @1
    @4
    wcel
    #
    @6
    @0
    @2
    simpl
    @3
    @1
    cc
    wcel
    #
    @2
    wa
    @9
    @0
    @10
    @2
    cA
    coscl
    anim1i
    @1
    cc
    cc0
    eldifsn
    sylibr
    cc
    cc
    ccos
    wf
    ccos
    cc
    wfn
    @6
    @0
    @9
    wa
    wb
    cosf
    cc
    cc
    ccos
    ffn
    cc
    cA
    @4
    ccos
    elpreima
    mp2b
    sylanbrc
    vx
    cA
    vx
    cv
    #
    csin
    cfv
    #
    @11
    ccos
    cfv
    #
    cdiv
    co
    @8
    @5
    ctan
    @11
    cA
    wceq
    @12
    @7
    @13
    @1
    cdiv
    @11
    cA
    csin
    fveq2
    @11
    cA
    ccos
    fveq2
    oveq12d
    vx
    df-tan
    @7
    @1
    cdiv
    ovex
    fvmpt
    syl
end
