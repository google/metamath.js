include "cnv.mm"
include "wcel.mm"
include "w3a.mm"
include "co.mm"
include "c1.mm"
include "cneg.mm"
include "cns.mm"
include "cfv.mm"
include "wceq.mm"
include "simp1.mm"
include "nvgcl.mm"
include "simp2.mm"
include "eqid.mm"
include "nvmval.mm"
include "syl3anc.mm"
include "simp3.mm"
include "cc.mm"
include "neg1cn.mm"
include "nvscl.mm"
include "mp3an2.mm"
include "3adant3.mm"
include "nvadd32.mm"
include "syl13anc.mm"
include "cn0v.mm"
include "nvrinv.mm"
include "oveq1d.mm"
include "nv0lid.mm"
include "3adant2.mm"
include "eqtrd.mm"

theorem nvpncan2
  let cA: class A
  let cB: class B
  let cU: class U
  let cG: class G
  let cM: class M
  let cX: class X
  assume nvpncan2.1: |- X = ( BaseSet ` U )
  assume nvpncan2.2: |- G = ( +v ` U )
  assume nvpncan2.3: |- M = ( -v ` U )


  assert |- ( ( U e. NrmCVec /\ A e. X /\ B e. X ) -> ( ( A G B ) M A ) = B )

  proof
    cU
    cnv
    wcel
    #
    cA
    cX
    wcel
    #
    cB
    cX
    wcel
    #
    w3a
    #
    cA
    cB
    cG
    co
    #
    cA
    cM
    co
    #
    @4
    c1
    cneg
    #
    cA
    cU
    cns
    cfv
    #
    co
    #
    cG
    co
    #
    cB
    @3
    @0
    @4
    cX
    wcel
    @1
    @5
    @9
    wceq
    @0
    @1
    @2
    simp1
    #
    cA
    cB
    cU
    cG
    cX
    nvpncan2.1
    nvpncan2.2
    nvgcl
    @0
    @1
    @2
    simp2
    #
    @4
    cA
    @7
    cU
    cG
    cM
    cX
    nvpncan2.1
    nvpncan2.2
    @7
    eqid
    #
    nvpncan2.3
    nvmval
    syl3anc
    @3
    @9
    cA
    @8
    cG
    co
    #
    cB
    cG
    co
    #
    cB
    @3
    @0
    @1
    @2
    @8
    cX
    wcel
    #
    @9
    @14
    wceq
    @10
    @11
    @0
    @1
    @2
    simp3
    @0
    @1
    @15
    @2
    @0
    @6
    cc
    wcel
    @1
    @15
    neg1cn
    @6
    cA
    @7
    cU
    cX
    nvpncan2.1
    @12
    nvscl
    mp3an2
    3adant3
    cA
    cB
    @8
    cU
    cG
    cX
    nvpncan2.1
    nvpncan2.2
    nvadd32
    syl13anc
    @3
    @14
    cU
    cn0v
    cfv
    #
    cB
    cG
    co
    #
    cB
    @3
    @13
    @16
    cB
    cG
    @0
    @1
    @13
    @16
    wceq
    @2
    cA
    @7
    cU
    cG
    cX
    @16
    nvpncan2.1
    nvpncan2.2
    @12
    @16
    eqid
    #
    nvrinv
    3adant3
    oveq1d
    @0
    @2
    @17
    cB
    wceq
    @1
    cB
    cU
    cG
    cX
    @16
    nvpncan2.1
    nvpncan2.2
    @18
    nv0lid
    3adant2
    eqtrd
    eqtrd
    eqtrd
end
