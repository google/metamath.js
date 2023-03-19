include "cword.mm"
include "wcel.mm"
include "cz.mm"
include "wa.mm"
include "cc0.mm"
include "clt.mm"
include "wbr.mm"
include "chash.mm"
include "cfv.mm"
include "cle.mm"
include "wo.mm"
include "cdm.mm"
include "wn.mm"
include "c0.mm"
include "wceq.mm"
include "wi.mm"
include "cfzo.mm"
include "co.mm"
include "wrddm.mm"
include "lencl.mm"
include "nn0zd.mm"
include "wnel.mm"
include "wb.mm"
include "simpr.mm"
include "0zd.mm"
include "simpl.mm"
include "nelfzo.mm"
include "syl3anc.mm"
include "biimpar.mm"
include "df-nel.mm"
include "sylib.mm"
include "eleq2.mm"
include "notbid.mm"
include "syl5ibr.mm"
include "exp4c.mm"
include "sylc.mm"
include "imp.mm"
include "ndmfv.mm"
include "syl6.mm"

theorem wrdsymb0
  let cI: class I
  let cV: class V
  let cW: class W


  assert |- ( ( W e. Word V /\ I e. ZZ ) -> ( ( I < 0 \/ ( # ` W ) <_ I ) -> ( W ` I ) = (/) ) )

  proof
    cW
    cV
    cword
    wcel
    #
    cI
    cz
    wcel
    #
    wa
    cI
    cc0
    clt
    wbr
    cW
    chash
    cfv
    #
    cI
    cle
    wbr
    wo
    #
    cI
    cW
    cdm
    #
    wcel
    #
    wn
    #
    cI
    cW
    cfv
    c0
    wceq
    @0
    @1
    @3
    @6
    wi
    #
    @0
    @4
    cc0
    @2
    cfzo
    co
    #
    wceq
    #
    @2
    cz
    wcel
    #
    @1
    @7
    wi
    cV
    cW
    wrddm
    @0
    @2
    cV
    cW
    lencl
    nn0zd
    @9
    @10
    @1
    @3
    @6
    @10
    @1
    wa
    #
    @3
    wa
    #
    @6
    @9
    cI
    @8
    wcel
    #
    wn
    #
    @12
    cI
    @8
    wnel
    #
    @14
    @11
    @15
    @3
    @11
    @1
    cc0
    cz
    wcel
    @10
    @15
    @3
    wb
    @10
    @1
    simpr
    @11
    0zd
    @10
    @1
    simpl
    cI
    cc0
    @2
    nelfzo
    syl3anc
    biimpar
    cI
    @8
    df-nel
    sylib
    @9
    @5
    @13
    @4
    @8
    cI
    eleq2
    notbid
    syl5ibr
    exp4c
    sylc
    imp
    cI
    cW
    ndmfv
    syl6
end
