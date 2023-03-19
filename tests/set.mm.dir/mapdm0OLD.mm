include "wcel.mm"
include "c0.mm"
include "cmap.mm"
include "co.mm"
include "csn.mm"
include "wceq.mm"
include "cv.mm"
include "wral.mm"
include "wa.mm"
include "wf.mm"
include "cvv.mm"
include "wb.mm"
include "0ex.mm"
include "elmapg.mm"
include "mpan2.mm"
include "biimpa.mm"
include "f0bi.mm"
include "sylib.mm"
include "ralrimiva.mm"
include "wne.mm"
include "f0.mm"
include "a1i.mm"
include "id.mm"
include "syl2anc.mm"
include "mpbird.mm"
include "ne0i.mm"
include "syl.mm"
include "eqsn.mm"

theorem mapdm0OLD
  let cA: class A
  let cV: class V
  let vf: setvar f


  assert |- ( A e. V -> ( A ^m (/) ) = { (/) } )

  proof
    cA
    cV
    wcel
    #
    cA
    c0
    cmap
    co
    #
    c0
    csn
    wceq
    #
    vf
    cv
    #
    c0
    wceq
    #
    vf
    @1
    wral
    #
    @0
    @4
    vf
    @1
    @0
    @3
    @1
    wcel
    #
    wa
    c0
    cA
    @3
    wf
    #
    @4
    @0
    @6
    @7
    @0
    c0
    cvv
    wcel
    #
    @6
    @7
    wb
    0ex
    cA
    c0
    @3
    cV
    cvv
    elmapg
    mpan2
    biimpa
    @3
    cA
    f0bi
    sylib
    ralrimiva
    @0
    @1
    c0
    wne
    #
    @2
    @5
    wb
    @0
    c0
    @1
    wcel
    #
    @9
    @0
    @10
    c0
    cA
    c0
    wf
    #
    @11
    @0
    cA
    f0
    a1i
    @0
    @0
    @8
    @10
    @11
    wb
    @0
    id
    @8
    @0
    0ex
    a1i
    cA
    c0
    c0
    cV
    cvv
    elmapg
    syl2anc
    mpbird
    @1
    c0
    ne0i
    syl
    vf
    @1
    c0
    eqsn
    syl
    mpbird
end
