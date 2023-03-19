include "cxr.mm"
include "wcel.mm"
include "wa.mm"
include "cle.mm"
include "wbr.mm"
include "cop.mm"
include "clt.mm"
include "ccnv.mm"
include "wn.mm"
include "df-br.mm"
include "cxp.mm"
include "wb.mm"
include "opelxpi.mm"
include "cdif.mm"
include "df-le.mm"
include "eleq2i.mm"
include "eldif.mm"
include "bitri.mm"
include "baib.mm"
include "syl.mm"
include "syl5bb.mm"
include "opelcnvg.mm"
include "syl6rbbr.mm"
include "notbid.mm"
include "bitr4d.mm"

theorem xrlenlt
  let cA: class A
  let cB: class B


  assert |- ( ( A e. RR* /\ B e. RR* ) -> ( A <_ B <-> -. B < A ) )

  proof
    cA
    cxr
    wcel
    cB
    cxr
    wcel
    wa
    #
    cA
    cB
    cle
    wbr
    #
    cA
    cB
    cop
    #
    clt
    ccnv
    #
    wcel
    #
    wn
    #
    cB
    cA
    clt
    wbr
    #
    wn
    @1
    @2
    cle
    wcel
    #
    @0
    @5
    cA
    cB
    cle
    df-br
    @0
    @2
    cxr
    cxr
    cxp
    #
    wcel
    #
    @7
    @5
    wb
    cA
    cB
    cxr
    cxr
    opelxpi
    @7
    @9
    @5
    @7
    @2
    @8
    @3
    cdif
    #
    wcel
    @9
    @5
    wa
    cle
    @10
    @2
    df-le
    eleq2i
    @2
    @8
    @3
    eldif
    bitri
    baib
    syl
    syl5bb
    @0
    @6
    @4
    @0
    @4
    cB
    cA
    cop
    clt
    wcel
    @6
    cA
    cB
    cxr
    cxr
    clt
    opelcnvg
    cB
    cA
    clt
    df-br
    syl6rbbr
    notbid
    bitr4d
end
