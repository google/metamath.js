include "cword.mm"
include "wcel.mm"
include "cn.mm"
include "wa.mm"
include "cc0.mm"
include "cfv.mm"
include "cs1.mm"
include "cconcat.mm"
include "co.mm"
include "cwwlks.mm"
include "chash.mm"
include "c1.mm"
include "caddc.mm"
include "wceq.mm"
include "cclwwlk.mm"
include "cwwlksn.mm"
include "cclwwlkn.mm"
include "cn0.mm"
include "wb.mm"
include "nnnn0.mm"
include "ccatws1lenp1b.mm"
include "sylan2.mm"
include "anbi2d.mm"
include "c0.mm"
include "wne.mm"
include "simpl.mm"
include "wi.mm"
include "eleq1.mm"
include "len0nnbi.mm"
include "biimprcd.mm"
include "syl6bir.mm"
include "com13.mm"
include "imp31.mm"
include "clwwlkwwlksb.mm"
include "syl2an2r.mm"
include "bicomd.mm"
include "ex.mm"
include "pm5.32rd.mm"
include "bitrd.mm"
include "adantl.mm"
include "iswwlksn.mm"
include "syl.mm"
include "isclwwlkn.mm"
include "a1i.mm"
include "3bitr4rd.mm"

theorem clwwlknwwlksnb
  let cG: class G
  let cN: class N
  let cV: class V
  let cW: class W
  let vi: setvar i
  assume clwwlkwwlksb.v: |- V = ( Vtx ` G )


  assert |- ( ( W e. Word V /\ N e. NN ) -> ( W e. ( N ClWWalksN G ) <-> ( W ++ <" ( W ` 0 ) "> ) e. ( N WWalksN G ) ) )

  proof
    cW
    cV
    cword
    wcel
    #
    cN
    cn
    wcel
    #
    wa
    #
    cW
    cc0
    cW
    cfv
    #
    cs1
    cconcat
    co
    #
    cG
    cwwlks
    cfv
    wcel
    #
    @4
    chash
    cfv
    cN
    c1
    caddc
    co
    wceq
    #
    wa
    #
    cW
    cG
    cclwwlk
    cfv
    wcel
    #
    cW
    chash
    cfv
    #
    cN
    wceq
    #
    wa
    #
    @4
    cN
    cG
    cwwlksn
    co
    wcel
    #
    cW
    cN
    cG
    cclwwlkn
    co
    wcel
    #
    @2
    @7
    @5
    @10
    wa
    @11
    @2
    @6
    @10
    @5
    @1
    @0
    cN
    cn0
    wcel
    #
    @6
    @10
    wb
    cN
    nnnn0
    #
    cN
    cV
    cW
    @3
    ccatws1lenp1b
    sylan2
    anbi2d
    @2
    @10
    @5
    @8
    @2
    @10
    @5
    @8
    wb
    @2
    @10
    wa
    @8
    @5
    @2
    @0
    @10
    cW
    c0
    wne
    #
    @8
    @5
    wb
    @0
    @1
    simpl
    @0
    @1
    @10
    @16
    @10
    @1
    @0
    @16
    @10
    @1
    @9
    cn
    wcel
    #
    @0
    @16
    wi
    @9
    cN
    cn
    eleq1
    @0
    @16
    @17
    cV
    cW
    len0nnbi
    biimprcd
    syl6bir
    com13
    imp31
    cG
    cV
    cW
    clwwlkwwlksb.v
    clwwlkwwlksb
    syl2an2r
    bicomd
    ex
    pm5.32rd
    bitrd
    @2
    @14
    @12
    @7
    wb
    @1
    @14
    @0
    @15
    adantl
    cG
    cN
    @4
    iswwlksn
    syl
    @13
    @11
    wb
    @2
    cG
    cN
    cW
    isclwwlkn
    a1i
    3bitr4rd
end
