include "clt.mm"
include "wbr.mm"
include "wn.mm"
include "wceq.mm"
include "wa.mm"
include "cxr.mm"
include "wcel.mm"
include "wb.mm"
include "eqeltrrd.mm"
include "xrlttri3.mm"
include "syl2anc.mm"
include "mpbid.mm"
include "simpld.mm"

theorem xreqnltd
  let wph: wff ph
  let cA: class A
  let cB: class B
  assume xreqnltd.1: |- ( ph -> A e. RR* )
  assume xreqnltd.2: |- ( ph -> A = B )


  assert |- ( ph -> -. A < B )

  proof
    wph
    cA
    cB
    clt
    wbr
    wn
    #
    cB
    cA
    clt
    wbr
    wn
    #
    wph
    cA
    cB
    wceq
    #
    @0
    @1
    wa
    #
    xreqnltd.2
    wph
    cA
    cxr
    wcel
    cB
    cxr
    wcel
    @2
    @3
    wb
    xreqnltd.1
    wph
    cA
    cB
    cxr
    xreqnltd.2
    xreqnltd.1
    eqeltrrd
    cA
    cB
    xrlttri3
    syl2anc
    mpbid
    simpld
end
