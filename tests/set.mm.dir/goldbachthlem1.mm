include "cn0.mm"
include "wcel.mm"
include "clt.mm"
include "wbr.mm"
include "w3a.mm"
include "cfmtno.mm"
include "cfv.mm"
include "cmin.mm"
include "co.mm"
include "caddc.mm"
include "c2.mm"
include "cdvds.mm"
include "cn.mm"
include "simp2.mm"
include "cz.mm"
include "wb.mm"
include "nn0z.mm"
include "znnsub.mm"
include "syl2anr.mm"
include "biimp3a.mm"
include "fmtnodvds.mm"
include "syl2anc.mm"
include "cc.mm"
include "wa.mm"
include "wceq.mm"
include "nn0cn.mm"
include "anim12ci.mm"
include "3adant3.mm"
include "pncan3.mm"
include "syl.mm"
include "eqcomd.mm"
include "fveq2d.mm"
include "oveq1d.mm"
include "breqtrrd.mm"

theorem goldbachthlem1
  let cM: class M
  let cN: class N
  let vk: setvar k
  let vx: setvar x


  assert |- ( ( N e. NN0 /\ M e. NN0 /\ M < N ) -> ( FermatNo ` M ) || ( ( FermatNo ` N ) - 2 ) )

  proof
    cN
    cn0
    wcel
    #
    cM
    cn0
    wcel
    #
    cM
    cN
    clt
    wbr
    #
    w3a
    #
    cM
    cfmtno
    cfv
    #
    cM
    cN
    cM
    cmin
    co
    #
    caddc
    co
    #
    cfmtno
    cfv
    #
    c2
    cmin
    co
    #
    cN
    cfmtno
    cfv
    #
    c2
    cmin
    co
    cdvds
    @3
    @1
    @5
    cn
    wcel
    #
    @4
    @8
    cdvds
    wbr
    @0
    @1
    @2
    simp2
    @0
    @1
    @2
    @10
    @1
    cM
    cz
    wcel
    cN
    cz
    wcel
    @2
    @10
    wb
    @0
    cM
    nn0z
    cN
    nn0z
    cM
    cN
    znnsub
    syl2anr
    biimp3a
    @5
    cM
    fmtnodvds
    syl2anc
    @3
    @9
    @7
    c2
    cmin
    @3
    cN
    @6
    cfmtno
    @3
    @6
    cN
    @3
    cM
    cc
    wcel
    #
    cN
    cc
    wcel
    #
    wa
    #
    @6
    cN
    wceq
    @0
    @1
    @13
    @2
    @0
    @12
    @1
    @11
    cN
    nn0cn
    cM
    nn0cn
    anim12ci
    3adant3
    cM
    cN
    pncan3
    syl
    eqcomd
    fveq2d
    oveq1d
    breqtrrd
end
