include "c2.mm"
include "wceq.mm"
include "cn.mm"
include "wcel.mm"
include "w3a.mm"
include "cexp.mm"
include "co.mm"
include "c1.mm"
include "cmin.mm"
include "cdvds.mm"
include "wbr.mm"
include "wn.mm"
include "wne.mm"
include "cz.mm"
include "2z.mm"
include "simp2.mm"
include "iddvdsexp.mm"
include "sylancr.mm"
include "wb.mm"
include "oveq1.mm"
include "breq2d.mm"
include "3ad2ant1.mm"
include "mpbird.mm"
include "mpan.mm"
include "notnotd.mm"
include "2nn.mm"
include "a1i.mm"
include "nnnn0.mm"
include "nnexpcld.mm"
include "nnzd.mm"
include "oddm1even.mm"
include "syl.mm"
include "mtbid.mm"
include "3ad2ant3.mm"
include "nbrne1.mm"
include "syl2anc.mm"
include "necomd.mm"

theorem lighneallem1
  let cP: class P
  let cM: class M
  let cN: class N
  let vk: setvar k
  let vx: setvar x


  assert |- ( ( P = 2 /\ M e. NN /\ N e. NN ) -> ( ( 2 ^ N ) - 1 ) =/= ( P ^ M ) )

  proof
    cP
    c2
    wceq
    #
    cM
    cn
    wcel
    #
    cN
    cn
    wcel
    #
    w3a
    #
    cP
    cM
    cexp
    co
    #
    c2
    cN
    cexp
    co
    #
    c1
    cmin
    co
    #
    @3
    c2
    @4
    cdvds
    wbr
    #
    c2
    @6
    cdvds
    wbr
    #
    wn
    #
    @4
    @6
    wne
    @3
    @7
    c2
    c2
    cM
    cexp
    co
    #
    cdvds
    wbr
    #
    @3
    c2
    cz
    wcel
    #
    @1
    @11
    2z
    @0
    @1
    @2
    simp2
    c2
    cM
    iddvdsexp
    sylancr
    @0
    @1
    @7
    @11
    wb
    @2
    @0
    @4
    @10
    c2
    cdvds
    cP
    c2
    cM
    cexp
    oveq1
    breq2d
    3ad2ant1
    mpbird
    @2
    @0
    @9
    @1
    @2
    c2
    @5
    cdvds
    wbr
    #
    wn
    #
    @8
    @2
    @13
    @12
    @2
    @13
    2z
    c2
    cN
    iddvdsexp
    mpan
    notnotd
    @2
    @5
    cz
    wcel
    @14
    @8
    wb
    @2
    @5
    @2
    c2
    cN
    c2
    cn
    wcel
    @2
    2nn
    a1i
    cN
    nnnn0
    nnexpcld
    nnzd
    @5
    oddm1even
    syl
    mtbid
    3ad2ant3
    c2
    @4
    @6
    cdvds
    nbrne1
    syl2anc
    necomd
end
