include "cn0.mm"
include "wcel.mm"
include "cn.mm"
include "wa.mm"
include "csgm.mm"
include "co.mm"
include "cv.mm"
include "cdvds.mm"
include "wbr.mm"
include "crab.mm"
include "cexp.mm"
include "csu.mm"
include "cz.mm"
include "wceq.mm"
include "nn0z.mm"
include "sgmval2.mm"
include "sylan.mm"
include "cc0.mm"
include "clt.mm"
include "c1.mm"
include "cfz.mm"
include "cfn.mm"
include "wss.mm"
include "fzfid.mm"
include "dvdsssfz1.mm"
include "adantl.mm"
include "ssfi.mm"
include "syl2anc.mm"
include "elrabi.mm"
include "simpl.mm"
include "nnexpcl.mm"
include "syl2anr.mm"
include "nnzd.mm"
include "fsumzcl.mm"
include "c0.mm"
include "wne.mm"
include "wrex.mm"
include "nnz.mm"
include "iddvds.mm"
include "syl.mm"
include "breq1.mm"
include "rspcev.mm"
include "mpdan.mm"
include "rabn0.mm"
include "sylibr.mm"
include "nnrpd.mm"
include "fsumrpcl.mm"
include "rpgt0d.mm"
include "elnnz.mm"
include "sylanbrc.mm"
include "eqeltrd.mm"

theorem sgmnncl
  let cA: class A
  let cB: class B
  let vk: setvar k
  let vn: setvar n
  let vp: setvar p
  let vq: setvar q
  let vs: setvar s
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cK: class K
  let cM: class M
  let cN: class N
  let cS: class S
  let cP: class P


  assert |- ( ( A e. NN0 /\ B e. NN ) -> ( A sigma B ) e. NN )

  proof
    cA
    cn0
    wcel
    #
    cB
    cn
    wcel
    #
    wa
    #
    cA
    cB
    csgm
    co
    #
    vp
    cv
    #
    cB
    cdvds
    wbr
    #
    vp
    cn
    crab
    #
    vk
    cv
    #
    cA
    cexp
    co
    #
    vk
    csu
    #
    cn
    @0
    cA
    cz
    wcel
    @1
    @3
    @9
    wceq
    cA
    nn0z
    cA
    cB
    vk
    vp
    sgmval2
    sylan
    @2
    @9
    cz
    wcel
    cc0
    @9
    clt
    wbr
    @9
    cn
    wcel
    @2
    @6
    @8
    vk
    @2
    c1
    cB
    cfz
    co
    #
    cfn
    wcel
    @6
    @10
    wss
    #
    @6
    cfn
    wcel
    @2
    c1
    cB
    fzfid
    @1
    @11
    @0
    cB
    vp
    dvdsssfz1
    adantl
    @10
    @6
    ssfi
    syl2anc
    #
    @2
    @7
    @6
    wcel
    #
    wa
    #
    @8
    @13
    @7
    cn
    wcel
    @0
    @8
    cn
    wcel
    @2
    @5
    vp
    @7
    cn
    elrabi
    @0
    @1
    simpl
    @7
    cA
    nnexpcl
    syl2anr
    #
    nnzd
    fsumzcl
    @2
    @9
    @2
    @6
    @8
    vk
    @12
    @1
    @6
    c0
    wne
    #
    @0
    @1
    @5
    vp
    cn
    wrex
    #
    @16
    @1
    cB
    cB
    cdvds
    wbr
    #
    @17
    @1
    cB
    cz
    wcel
    @18
    cB
    nnz
    cB
    iddvds
    syl
    @5
    @18
    vp
    cB
    cn
    @4
    cB
    cB
    cdvds
    breq1
    rspcev
    mpdan
    @5
    vp
    cn
    rabn0
    sylibr
    adantl
    @14
    @8
    @15
    nnrpd
    fsumrpcl
    rpgt0d
    @9
    elnnz
    sylanbrc
    eqeltrd
end
