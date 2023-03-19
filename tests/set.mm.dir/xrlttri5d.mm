include "clt.mm"
include "wbr.mm"
include "wn.mm"
include "wo.mm"
include "wa.mm"
include "wceq.mm"
include "neneqd.mm"
include "cxr.mm"
include "wcel.mm"
include "wb.mm"
include "xrlttri3.mm"
include "syl2anc.mm"
include "mtbid.mm"
include "oran.mm"
include "sylibr.mm"
include "jca.mm"
include "pm5.61.mm"
include "sylib.mm"
include "simpld.mm"

theorem xrlttri5d
  let wph: wff ph
  let cA: class A
  let cB: class B
  assume xrlttri5d.a: |- ( ph -> A e. RR* )
  assume xrlttri5d.b: |- ( ph -> B e. RR* )
  assume xrlttri5d.aneb: |- ( ph -> A =/= B )
  assume xrlttri5d.nlt: |- ( ph -> -. B < A )


  assert |- ( ph -> A < B )

  proof
    wph
    cA
    cB
    clt
    wbr
    #
    cB
    cA
    clt
    wbr
    #
    wn
    #
    wph
    @0
    @1
    wo
    #
    @2
    wa
    @0
    @2
    wa
    wph
    @3
    @2
    wph
    @0
    wn
    @2
    wa
    #
    wn
    @3
    wph
    cA
    cB
    wceq
    #
    @4
    wph
    cA
    cB
    xrlttri5d.aneb
    neneqd
    wph
    cA
    cxr
    wcel
    cB
    cxr
    wcel
    @5
    @4
    wb
    xrlttri5d.a
    xrlttri5d.b
    cA
    cB
    xrlttri3
    syl2anc
    mtbid
    @0
    @1
    oran
    sylibr
    xrlttri5d.nlt
    jca
    @0
    @1
    pm5.61
    sylib
    simpld
end
