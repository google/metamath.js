include "cpnf.mm"
include "clt.mm"
include "wbr.mm"
include "wn.mm"
include "wceq.mm"
include "neneqd.mm"
include "cxr.mm"
include "wcel.mm"
include "wb.mm"
include "nltpnft.mm"
include "syl.mm"
include "mtbid.mm"
include "notnotb.mm"
include "sylibr.mm"

theorem nepnfltpnf
  let wph: wff ph
  let cA: class A
  assume nepnfltpnf.1: |- ( ph -> A =/= +oo )
  assume nepnfltpnf.2: |- ( ph -> A e. RR* )


  assert |- ( ph -> A < +oo )

  proof
    wph
    cA
    cpnf
    clt
    wbr
    #
    wn
    #
    wn
    @0
    wph
    cA
    cpnf
    wceq
    #
    @1
    wph
    cA
    cpnf
    nepnfltpnf.1
    neneqd
    wph
    cA
    cxr
    wcel
    @2
    @1
    wb
    nepnfltpnf.2
    cA
    nltpnft
    syl
    mtbid
    @0
    notnotb
    sylibr
end
